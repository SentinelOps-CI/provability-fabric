// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{anyhow, Context, Result};
use sidecar_watcher::utc_timestamp::UtcTimestamp;
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{Api, Client};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn};

/// Legacy-named accountant using additive composition, not a moments accountant.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MomentsAccountant {
    pub epsilon: f64,
    pub delta: f64,
    pub alpha: f64,
    pub queries: Vec<Query>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Query {
    pub epsilon: f64,
    pub delta: f64,
    pub timestamp: UtcTimestamp,
}

impl MomentsAccountant {
    pub fn new(epsilon: f64, delta: f64) -> Self {
        Self {
            epsilon,
            delta,
            alpha: 1.0,
            queries: Vec::new(),
        }
    }

    /// Add a query to the accountant
    pub fn add_query(&mut self, epsilon: f64, delta: f64) -> Result<()> {
        let (next_epsilon, next_delta) = self.proposed_totals(epsilon, delta)?;
        validate_cost(next_epsilon, next_delta)?;
        let query = Query {
            epsilon,
            delta,
            timestamp: UtcTimestamp::now(),
        };
        self.queries.push(query);
        self.epsilon = next_epsilon;
        self.delta = next_delta;

        Ok(())
    }

    fn proposed_totals(&self, epsilon: f64, delta: f64) -> Result<(f64, f64)> {
        validate_cost(epsilon, delta)?;
        validate_cost(self.epsilon, self.delta)?;
        Ok((upper_sum(self.epsilon, epsilon)?, upper_sum(self.delta, delta)?))
    }

    /// Check if budget is exhausted
    pub fn is_exhausted(&self, limit_epsilon: f64, limit_delta: f64) -> bool {
        self.epsilon >= limit_epsilon || self.delta >= limit_delta
    }

    /// Get remaining budget
    pub fn remaining_budget(&self, limit_epsilon: f64, limit_delta: f64) -> (f64, f64) {
        let remaining_epsilon = (limit_epsilon - self.epsilon).max(0.0);
        let remaining_delta = (limit_delta - self.delta).max(0.0);
        (remaining_epsilon, remaining_delta)
    }
}

fn validate_cost(epsilon: f64, delta: f64) -> Result<()> {
    if !epsilon.is_finite() || epsilon < 0.0 || !delta.is_finite() || !(0.0..=1.0).contains(&delta) {
        return Err(anyhow!("Invalid privacy cost or accumulator"));
    }
    Ok(())
}

// Round the sum upward only if the round-to-nearest result underestimates
// the exact sum of the binary64 operands. FastTwoSum uses ordered magnitudes.
// This conservatively accounts for represented inputs, not real-number
// interpretations of decimal input or proof of the mechanism's DP claim.
fn upper_sum(a: f64, b: f64) -> Result<f64> {
    let (large, small) = if a >= b { (a, b) } else { (b, a) };
    let sum = large + small;
    if !sum.is_finite() {
        return Err(anyhow!("Privacy cost overflow"));
    }
    let residual = small - (sum - large);
    let upper = if residual > 0.0 { sum.next_up() } else { sum };
    if !upper.is_finite() {
        return Err(anyhow!("Privacy cost overflow"));
    }
    Ok(upper)
}

/// Privacy budget configuration for a tenant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrivacyConfig {
    pub tenant_id: String,
    pub epsilon_limit: f64,
    pub delta_limit: f64,
    pub reset_period_hours: u32,
}

impl PrivacyConfig {
    fn validate(&self, key: &str) -> Result<()> {
        validate_cost(self.epsilon_limit, self.delta_limit)?;
        if key.is_empty() || self.tenant_id != key || self.reset_period_hours == 0 {
            return Err(anyhow!("Invalid privacy configuration identity or reset period"));
        }
        Ok(())
    }
}

/// Process-local additive privacy budget guard. No restart-safe or distributed
/// accounting guarantee is provided.
pub struct EpsilonGuard {
    /// Optional ConfigMap API; None when running outside a cluster/dev mode
    config_map_api: Option<Api<ConfigMap>>,
    accountants: Arc<RwLock<HashMap<String, MomentsAccountant>>>,
    configs: Arc<RwLock<HashMap<String, PrivacyConfig>>>,
}

impl EpsilonGuard {
    /// Create a guard. Missing Kubernetes configuration denies privacy charges.
    pub async fn new() -> Result<Self> {
        let config_map_api =
            match tokio::time::timeout(std::time::Duration::from_secs(2), Client::try_default())
                .await
            {
                Ok(Ok(client)) => {
                    let api: Api<ConfigMap> = Api::default_namespaced(client.clone());
                    Some(api)
                }
                Ok(Err(e)) => {
                    warn!(
                        "Kubernetes not detected; privacy charges unavailable: {}",
                        e
                    );
                    None
                }
                Err(_) => {
                    warn!(
                        "Kubernetes client init timed out; privacy charges unavailable"
                    );
                    None
                }
            };

        Ok(Self {
            config_map_api,
            accountants: Arc::new(RwLock::new(HashMap::new())),
            configs: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    /// Load a complete configuration snapshot, denying charges after a failed refresh.
    pub async fn load_configs(&self) -> Result<()> {
        let mut configs = self.configs.write().await;
        configs.clear();
        let Some(api) = &self.config_map_api else {
            return Err(anyhow!("Privacy configuration unavailable"));
        };

        let config_map = tokio::time::timeout(
            std::time::Duration::from_secs(5), api.get("privacy-config"))
            .await.context("Privacy ConfigMap request timed out")?
            .context("Failed to get privacy ConfigMap")?;

        let data = config_map
            .data
            .ok_or_else(|| anyhow!("No data in privacy ConfigMap"))?;

        let mut snapshot = HashMap::new();
        for (tenant_id, config_json) in &data {
            let config: PrivacyConfig = serde_json::from_str(config_json)
                .with_context(|| format!("Failed to parse config for tenant {}", tenant_id))?;
            config.validate(tenant_id)?;
            snapshot.insert(tenant_id.clone(), config);
        }
        *configs = snapshot;
        info!("Loaded {} privacy configurations", configs.len());
        Ok(())
    }

    /// Check if a query is allowed for a tenant
    pub async fn check_query(
        &self,
        tenant_id: &str,
        query_epsilon: f64,
        query_delta: f64,
    ) -> Result<bool> {
        validate_cost(query_epsilon, query_delta)?;
        let configs = self.configs.read().await;
        let config = configs.get(tenant_id)
            .ok_or_else(|| anyhow!("No privacy config for tenant {}", tenant_id))?;
        config.validate(tenant_id)?;

        // Get or create accountant for tenant
        let mut accountants = self.accountants.write().await;
        let accountant = accountants
            .entry(tenant_id.to_string())
            .or_insert_with(|| MomentsAccountant::new(0.0, 0.0));

        // A zero-cost coordinate is permitted at its limit (in particular,
        // pure DP with delta = 0). Positive costs must fit both limits.
        let (test_epsilon, test_delta) = accountant.proposed_totals(query_epsilon, query_delta)?;

        if test_epsilon > config.epsilon_limit || test_delta > config.delta_limit {
            warn!(
                "Query rejected for tenant {}: epsilon={}, delta={} exceeds limits epsilon={}, delta={}",
                tenant_id, test_epsilon, test_delta, config.epsilon_limit, config.delta_limit
            );
            return Ok(false);
        }

        // Add query to accountant
        accountant.add_query(query_epsilon, query_delta)?;

        info!(
            "Query allowed for tenant {}: epsilon={}, delta={}, remaining epsilon={}, delta={}",
            tenant_id,
            query_epsilon,
            query_delta,
            config.epsilon_limit - test_epsilon,
            config.delta_limit - test_delta
        );

        Ok(true)
    }

    /// Get remaining budget for a tenant
    pub async fn get_remaining_budget(&self, tenant_id: &str) -> Result<(f64, f64)> {
        let configs = self.configs.read().await;
        let config = configs.get(tenant_id)
            .ok_or_else(|| anyhow!("No privacy config for tenant {}", tenant_id))?;
        config.validate(tenant_id)?;

        let accountants = self.accountants.read().await;
        let default_accountant = MomentsAccountant::new(0.0, 0.0);
        let accountant = accountants.get(tenant_id).unwrap_or(&default_accountant);

        Ok(accountant.remaining_budget(config.epsilon_limit, config.delta_limit))
    }

    /// Reset budget for a tenant (called periodically)
    pub async fn reset_budget(&self, tenant_id: &str) -> Result<()> {
        let mut accountants = self.accountants.write().await;
        accountants.remove(tenant_id);

        info!("Reset privacy budget for tenant {}", tenant_id);
        Ok(())
    }

    /// Export privacy metrics for monitoring
    pub async fn export_metrics(&self) -> Result<HashMap<String, PrivacyMetrics>> {
        let mut metrics = HashMap::new();

        let configs = self.configs.read().await;
        let accountants = self.accountants.read().await;

        let default_accountant = MomentsAccountant::new(0.0, 0.0);
        for (tenant_id, config) in configs.iter() {
            let accountant = accountants.get(tenant_id).unwrap_or(&default_accountant);

            let (remaining_epsilon, remaining_delta) =
                accountant.remaining_budget(config.epsilon_limit, config.delta_limit);

            metrics.insert(
                tenant_id.clone(),
                PrivacyMetrics {
                    tenant_id: tenant_id.clone(),
                    epsilon_used: accountant.epsilon,
                    epsilon_limit: config.epsilon_limit,
                    epsilon_remaining: remaining_epsilon,
                    delta_used: accountant.delta,
                    delta_limit: config.delta_limit,
                    delta_remaining: remaining_delta,
                    query_count: accountant.queries.len() as u64,
                },
            );
        }

        Ok(metrics)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrivacyMetrics {
    pub tenant_id: String,
    pub epsilon_used: f64,
    pub epsilon_limit: f64,
    pub epsilon_remaining: f64,
    pub delta_used: f64,
    pub delta_limit: f64,
    pub delta_remaining: f64,
    pub query_count: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_moments_accountant() {
        let mut accountant = MomentsAccountant::new(0.0, 0.0);

        // Add queries
        accountant.add_query(0.1, 0.01).unwrap();
        accountant.add_query(0.2, 0.02).unwrap();

        // Decimal fractions are inexact in binary floating point. Only the
        // numerical test oracle changes; budget enforcement is unmodified.
        assert!((accountant.epsilon - 0.3).abs() < 4.0 * f64::EPSILON);
        assert!((accountant.delta - 0.03).abs() < 4.0 * f64::EPSILON);

        // Check budget limits
        assert!(!accountant.is_exhausted(1.0, 0.1));
        assert!(accountant.is_exhausted(0.2, 0.1));

        let (remaining_epsilon, remaining_delta) = accountant.remaining_budget(1.0, 0.1);
        assert!((remaining_epsilon - 0.7).abs() < 4.0 * f64::EPSILON);
        assert!((remaining_delta - 0.07).abs() < 4.0 * f64::EPSILON);
    }

    #[tokio::test]
    async fn test_kubernetes_configmap_over_loopback() {
        use axum::{routing::get, Json, Router};
        use serde_json::json;

        // Exercise the actual Kubernetes HTTP client and typed ConfigMap
        // decoding without access to any live cluster or credentials.
        let configuration = json!({
            "tenant_id": "fixture-tenant", "epsilon_limit": 1.0,
            "delta_limit": 0.1, "reset_period_hours": 24
        }).to_string();
        let response = json!({
            "apiVersion": "v1", "kind": "ConfigMap",
            "metadata": {"name": "privacy-config", "namespace": "default"},
            "data": {"fixture-tenant": configuration}
        });
        let app = Router::new().route(
            "/api/v1/namespaces/default/configmaps/privacy-config",
            get(move || { let body = response.clone(); async move { Json(body) } }),
        );
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let address = listener.local_addr().unwrap();
        let task = tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
        let config = kube::Config::new(format!("http://{address}").parse().unwrap());
        let client = Client::try_from(config).unwrap();
        let guard = EpsilonGuard {
            config_map_api: Some(Api::default_namespaced(client)),
            accountants: Arc::new(RwLock::new(HashMap::new())),
            configs: Arc::new(RwLock::new(HashMap::new())),
        };
        tokio::time::timeout(std::time::Duration::from_secs(5), guard.load_configs())
            .await.unwrap().unwrap();
        assert!(guard.check_query("fixture-tenant", 0.5, 0.05).await.unwrap());
        assert!(!guard.check_query("fixture-tenant", 0.6, 0.06).await.unwrap());
        assert!(guard.check_query("unknown-tenant", 0.1, 0.01).await.is_err());
        task.abort();
    }

    /// Executed explicitly in the isolated TLS fixture workflow. Ordinary
    /// developer test runs do not provision a second system trust anchor.
    #[tokio::test]
    #[ignore = "requires isolated TLS endpoints and system CA fixture"]
    async fn test_kubernetes_configmap_configured_ca_is_exclusive() {
        let ca = std::fs::read(std::env::var("PF_KUBE_TEST_CA_DER").unwrap()).unwrap();
        let trusted = std::env::var("PF_KUBE_TEST_TRUSTED_URL").unwrap();
        let unrelated = std::env::var("PF_KUBE_TEST_UNRELATED_URL").unwrap();

        async fn guard(url: &str, ca: Option<Vec<Vec<u8>>>) -> EpsilonGuard {
            let mut config = kube::Config::new(url.parse().unwrap());
            config.root_cert = ca;
            config.accept_invalid_certs = false;
            let client = Client::try_from(config).unwrap();
            EpsilonGuard {
                config_map_api: Some(Api::default_namespaced(client)),
                accountants: Arc::new(RwLock::new(HashMap::new())),
                configs: Arc::new(RwLock::new(HashMap::new())),
            }
        }

        // Confirm the unrelated root really is trusted by the default
        // transport. Otherwise the rejection below would be vacuous.
        let system = guard(&unrelated, None).await;
        system.load_configs().await.expect("system CA positive control");
        assert!(system.check_query("fixture-tenant", 0.25, 0.01).await.unwrap());

        let explicit = guard(&trusted, Some(vec![ca.clone()])).await;
        explicit.load_configs().await.expect("configured CA positive control");
        assert!(explicit.check_query("fixture-tenant", 0.25, 0.01).await.unwrap());

        let wrong = guard(&unrelated, Some(vec![ca])).await;
        assert!(wrong.load_configs().await.is_err(), "unrelated system root was accepted");
        assert!(wrong.check_query("fixture-tenant", 0.0, 0.0).await.is_err());
    }

    #[tokio::test]
    async fn test_privacy_missing_config_and_invalid_costs_fail_closed() {
        let guard = EpsilonGuard {
            config_map_api: None,
            accountants: Arc::new(RwLock::new(HashMap::new())),
            configs: Arc::new(RwLock::new(HashMap::new())),
        };
        assert!(guard.check_query("tenant", 0.1, 0.01).await.is_err());
        assert!(guard.get_remaining_budget("tenant").await.is_err());
        guard.configs.write().await.insert("tenant".into(), PrivacyConfig {
            tenant_id: "tenant".into(), epsilon_limit: 1.0, delta_limit: 0.5,
            reset_period_hours: 24,
        });
        for (epsilon, delta) in [
            (-0.1, 0.0), (f64::NAN, 0.0), (f64::INFINITY, 0.0),
            (0.1, -0.1), (0.1, f64::NAN), (0.1, 1.1),
        ] {
            assert!(guard.check_query("tenant", epsilon, delta).await.is_err());
        }
        assert!(guard.accountants.read().await.is_empty());
        assert!(guard.check_query("tenant", 1.0, 0.25).await.unwrap());
        assert!(!guard.check_query("tenant", f64::MIN_POSITIVE, 0.0).await.unwrap());
        assert!(guard.load_configs().await.is_err());
        assert!(guard.check_query("tenant", 0.0, 0.0).await.is_err());
    }

    #[tokio::test]
    async fn test_concurrent_privacy_charges_respect_both_limits() {
        let guard = Arc::new(EpsilonGuard {
            config_map_api: None,
            accountants: Arc::new(RwLock::new(HashMap::new())),
            configs: Arc::new(RwLock::new(HashMap::new())),
        });
        guard.configs.write().await.insert("tenant".into(), PrivacyConfig {
            tenant_id: "tenant".into(), epsilon_limit: 1.0, delta_limit: 0.0,
            reset_period_hours: 24,
        });
        let mut tasks = tokio::task::JoinSet::new();
        for _ in 0..16 {
            let guard = guard.clone();
            tasks.spawn(async move { guard.check_query("tenant", 0.125, 0.0).await.unwrap() });
        }
        let mut accepted = 0;
        while let Some(result) = tasks.join_next().await {
            if result.unwrap() {
                accepted += 1;
            }
        }
        assert_eq!(accepted, 8);
        assert_eq!(guard.get_remaining_budget("tenant").await.unwrap(), (0.0, 0.0));
        assert!(guard.check_query("tenant", 0.0, 0.0).await.unwrap());
        assert!(!guard.check_query("tenant", 0.0, f64::MIN_POSITIVE).await.unwrap());
        assert_eq!(guard.accountants.read().await["tenant"].queries.len(), 9);
    }

    #[test]
    fn test_privacy_query_timestamp_wire_contract() {
        let legacy = r#"{"epsilon":0.25,"delta":0.01,"timestamp":"2023-11-14T22:13:20.100Z"}"#;
        let decoded: Query = serde_json::from_str(legacy).unwrap();
        assert_eq!(decoded.timestamp.timestamp(), 1_700_000_000);
        assert_eq!(serde_json::to_string(&decoded).unwrap(), legacy);
        let offset = legacy.replace("22:13:20.100Z", "23:13:20.100+01:00");
        assert_eq!(serde_json::from_str::<Query>(&offset).unwrap().timestamp, decoded.timestamp);
        for malformed in ["2023-02-30T00:00:00Z", "2016-12-31T23:59:60Z", "2023-11-14T22:13:20.1234567891Z"] {
            assert!(serde_json::from_str::<Query>(&legacy.replace("2023-11-14T22:13:20.100Z", malformed)).is_err());
        }
        let mut accountant = MomentsAccountant::new(0.0, 0.0);
        accountant.add_query(0.25, 0.01).unwrap();
        assert_eq!(accountant.queries.len(), 1);
        assert_eq!(accountant.epsilon, 0.25);
        assert_eq!(accountant.delta, 0.01);
        let encoded = serde_json::to_string(&accountant).unwrap();
        let roundtrip: MomentsAccountant = serde_json::from_str(&encoded).unwrap();
        assert_eq!(roundtrip.queries[0].timestamp, accountant.queries[0].timestamp);
        assert_eq!((roundtrip.epsilon, roundtrip.delta), (0.25, 0.01));
    }

    #[test]
    fn test_upper_sum_does_not_drop_small_positive_charges() {
        assert_eq!(upper_sum(1.0, f64::MIN_POSITIVE).unwrap(), 1.0f64.next_up());
        assert_eq!(upper_sum(0.25, 0.25).unwrap(), 0.5);
        assert_eq!(upper_sum(0.0, 0.25).unwrap(), 0.25);
        assert!(upper_sum(f64::MAX, f64::MAX).is_err());
        let mut accountant = MomentsAccountant::new(0.0, 0.0);
        assert!(accountant.add_query(-1.0, 0.0).is_err());
        assert!(accountant.queries.is_empty());
    }

    #[tokio::test]
    async fn test_epsilon_guard_budget_exhaustion() {
        let guard = EpsilonGuard::new().await.unwrap();
        let mut configs = guard.configs.write().await;
        configs.insert(
            "test-tenant".to_string(),
            PrivacyConfig {
                tenant_id: "test-tenant".to_string(),
                epsilon_limit: 1.0,
                delta_limit: 0.1,
                reset_period_hours: 24,
            },
        );
        drop(configs);

        assert!(guard.check_query("test-tenant", 0.5, 0.05).await.unwrap());
        assert!(!guard.check_query("test-tenant", 0.6, 0.06).await.unwrap());
    }

    #[tokio::test]
    async fn test_epsilon_guard_config_validation() {
        let config = PrivacyConfig {
            tenant_id: "tenant-a".to_string(),
            epsilon_limit: 2.0,
            delta_limit: 0.01,
            reset_period_hours: 24,
        };
        assert!(config.epsilon_limit > 0.0);
        assert!(config.delta_limit > 0.0);
        assert!(config.reset_period_hours > 0);
    }

    #[tokio::test]
    async fn test_privacy_metrics_export() {
        let guard = EpsilonGuard::new().await.unwrap();
        let mut configs = guard.configs.write().await;
        configs.insert(
            "metrics-tenant".to_string(),
            PrivacyConfig {
                tenant_id: "metrics-tenant".to_string(),
                epsilon_limit: 1.0,
                delta_limit: 0.1,
                reset_period_hours: 24,
            },
        );
        drop(configs);

        let _ = guard.check_query("metrics-tenant", 0.1, 0.01).await.unwrap();
        let metrics = guard.export_metrics().await.unwrap();
        assert!(metrics.contains_key("metrics-tenant"));
    }

    #[tokio::test]
    async fn test_epsilon_guard() {
        let guard = EpsilonGuard::new().await.unwrap();

        // Mock configuration
        let mut configs = guard.configs.write().await;
        configs.insert(
            "test-tenant".to_string(),
            PrivacyConfig {
                tenant_id: "test-tenant".to_string(),
                epsilon_limit: 1.0,
                delta_limit: 0.1,
                reset_period_hours: 24,
            },
        );
        drop(configs);

        // Test query allowance
        let allowed = guard.check_query("test-tenant", 0.5, 0.05).await.unwrap();
        assert!(allowed);

        let allowed = guard.check_query("test-tenant", 0.6, 0.06).await.unwrap();
        assert!(!allowed); // Should exceed budget
    }
}
