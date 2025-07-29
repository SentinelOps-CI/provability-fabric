// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use k8s_openapi::api::core::v1::ConfigMap;
use kube::{Api, Client};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn};

/// Moments Accountant for differential privacy budget tracking
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
    pub timestamp: chrono::DateTime<chrono::Utc>,
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
        let query = Query {
            epsilon,
            delta,
            timestamp: chrono::Utc::now(),
        };
        self.queries.push(query);
        
        // Update cumulative epsilon using composition
        self.epsilon += epsilon;
        self.delta += delta;
        
        Ok(())
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

/// Privacy budget configuration for a tenant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrivacyConfig {
    pub tenant_id: String,
    pub epsilon_limit: f64,
    pub delta_limit: f64,
    pub reset_period_hours: u32,
}

/// Epsilon guard for enforcing differential privacy budgets
pub struct EpsilonGuard {
    kube_client: Client,
    config_map_api: Api<ConfigMap>,
    accountants: Arc<RwLock<HashMap<String, MomentsAccountant>>>,
    configs: Arc<RwLock<HashMap<String, PrivacyConfig>>>,
}

impl EpsilonGuard {
    pub fn new() -> Result<Self> {
        let client = Client::try_default()
            .context("Failed to create Kubernetes client")?;
        
        let config_map_api: Api<ConfigMap> = Api::default_namespaced(client.clone());
        
        Ok(Self {
            kube_client: client,
            config_map_api,
            accountants: Arc::new(RwLock::new(HashMap::new())),
            configs: Arc::new(RwLock::new(HashMap::new())),
        })
    }

    /// Load privacy configurations from ConfigMap
    pub async fn load_configs(&self) -> Result<()> {
        let config_map = self.config_map_api
            .get("privacy-config")
            .await
            .context("Failed to get privacy ConfigMap")?;
        
        let data = config_map.data
            .ok_or_else(|| anyhow::anyhow!("No data in privacy ConfigMap"))?;
        
        let mut configs = self.configs.write().await;
        
        for (tenant_id, config_json) in data {
            let config: PrivacyConfig = serde_json::from_str(&config_json)
                .context(format!("Failed to parse config for tenant {}", tenant_id))?;
            configs.insert(tenant_id, config);
        }
        
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
        // Get tenant configuration
        let configs = self.configs.read().await;
        let config = configs.get(tenant_id)
            .ok_or_else(|| anyhow::anyhow!("No privacy config for tenant {}", tenant_id))?;
        
        // Get or create accountant for tenant
        let mut accountants = self.accountants.write().await;
        let accountant = accountants.entry(tenant_id.to_string()).or_insert_with(|| {
            MomentsAccountant::new(0.0, 0.0)
        });
        
        // Check if adding this query would exceed budget
        let test_epsilon = accountant.epsilon + query_epsilon;
        let test_delta = accountant.delta + query_delta;
        
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
            tenant_id, query_epsilon, query_delta,
            config.epsilon_limit - test_epsilon, config.delta_limit - test_delta
        );
        
        Ok(true)
    }

    /// Get remaining budget for a tenant
    pub async fn get_remaining_budget(&self, tenant_id: &str) -> Result<(f64, f64)> {
        let configs = self.configs.read().await;
        let config = configs.get(tenant_id)
            .ok_or_else(|| anyhow::anyhow!("No privacy config for tenant {}", tenant_id))?;
        
        let accountants = self.accountants.read().await;
        let accountant = accountants.get(tenant_id)
            .unwrap_or(&MomentsAccountant::new(0.0, 0.0));
        
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
        
        for (tenant_id, config) in configs.iter() {
            let accountant = accountants.get(tenant_id)
                .unwrap_or(&MomentsAccountant::new(0.0, 0.0));
            
            let (remaining_epsilon, remaining_delta) = accountant.remaining_budget(
                config.epsilon_limit, config.delta_limit
            );
            
            metrics.insert(tenant_id.clone(), PrivacyMetrics {
                tenant_id: tenant_id.clone(),
                epsilon_used: accountant.epsilon,
                epsilon_limit: config.epsilon_limit,
                epsilon_remaining: remaining_epsilon,
                delta_used: accountant.delta,
                delta_limit: config.delta_limit,
                delta_remaining: remaining_delta,
                query_count: accountant.queries.len() as u64,
            });
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
        
        assert_eq!(accountant.epsilon, 0.3);
        assert_eq!(accountant.delta, 0.03);
        
        // Check budget limits
        assert!(!accountant.is_exhausted(1.0, 0.1));
        assert!(accountant.is_exhausted(0.2, 0.1));
        
        let (remaining_epsilon, remaining_delta) = accountant.remaining_budget(1.0, 0.1);
        assert_eq!(remaining_epsilon, 0.7);
        assert_eq!(remaining_delta, 0.07);
    }

    #[tokio::test]
    async fn test_epsilon_guard() {
        let guard = EpsilonGuard::new().unwrap();
        
        // Mock configuration
        let mut configs = guard.configs.write().await;
        configs.insert("test-tenant".to_string(), PrivacyConfig {
            tenant_id: "test-tenant".to_string(),
            epsilon_limit: 1.0,
            delta_limit: 0.1,
            reset_period_hours: 24,
        });
        drop(configs);
        
        // Test query allowance
        let allowed = guard.check_query("test-tenant", 0.5, 0.05).await.unwrap();
        assert!(allowed);
        
        let allowed = guard.check_query("test-tenant", 0.6, 0.06).await.unwrap();
        assert!(!allowed); // Should exceed budget
    }
}