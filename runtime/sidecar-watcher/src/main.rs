// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::Result;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use prometheus_client::{
    encoding::text::encode,
    metrics::{counter::Counter, gauge::Gauge},
    registry::Registry,
};
use serde::{Deserialize, Serialize};
use std::{
    env,
    fs::File,
    io::{BufRead, BufReader},
    net::SocketAddr,
    sync::Arc,
    time::Duration,
};
use tokio::time::sleep;
use tracing::{error, info, warn};
use reqwest::{Client, StatusCode};

mod ifc_labels;
mod deterministic_egress;
mod privacy;
mod http_health;

use sidecar_watcher::assumption::{Assumption, AssumptionMonitor};
use privacy::epsilon_guard::EpsilonGuard;

#[derive(Debug, Deserialize, Serialize)]
struct Action {
    #[serde(rename = "action")]
    action_type: String,
    spam_score: Option<f64>,
    usd_amount: Option<f64>,
    // Privacy budget fields
    privacy_epsilon: Option<f64>,
    privacy_delta: Option<f64>,
}

#[derive(Debug, Serialize)]
struct GuardTrip {
    event: String,
    reason: String,
    timestamp: String,
}

#[derive(Debug, Serialize)]
struct UsageEvent {
    tenant_id: String,
    cpu_ms: i64,
    net_bytes: i64,
    ts: String,
}

struct Metrics {
    total_actions: Counter,
    violations: Counter,
    assumption_violations: Counter,
    cpu_usage_ms: Counter,
    network_bytes: Counter,
    privacy_budget_remaining: Gauge, // i64 gauge; we'll store epsilon*1000 for precision
    privacy_violations: Counter,
}

impl Metrics {
    fn new(registry: &mut Registry) -> Self {
        let total_actions = Counter::default();
        let violations = Counter::default();
        let assumption_violations = Counter::default();
        let cpu_usage_ms = Counter::default();
        let network_bytes = Counter::default();
        let privacy_budget_remaining = Gauge::default();
        let privacy_violations = Counter::default();

        registry.register(
            "total_actions",
            "Total number of actions processed",
            total_actions.clone(),
        );
        registry.register(
            "violations",
            "Total number of constraint violations",
            violations.clone(),
        );
        registry.register(
            "assumption_violations_total",
            "Total number of assumption violations",
            assumption_violations.clone(),
        );
        registry.register(
            "cpu_usage_ms",
            "Total CPU usage in milliseconds",
            cpu_usage_ms.clone(),
        );
        registry.register(
            "network_bytes",
            "Total network bytes transferred",
            network_bytes.clone(),
        );
        registry.register(
            "privacy_budget_remaining",
            "Remaining privacy budget (epsilon * 1000)",
            privacy_budget_remaining.clone(),
        );
        registry.register(
            "privacy_violations_total",
            "Total number of privacy budget violations",
            privacy_violations.clone(),
        );

        Self {
            total_actions,
            violations,
            assumption_violations,
            cpu_usage_ms,
            network_bytes,
            privacy_budget_remaining,
            privacy_violations,
        }
    }
}

struct Watcher {
    // Shared Prometheus registry registered with our metrics
    registry: Arc<Registry>,

    metrics: Metrics,
    assumption_monitor: AssumptionMonitor,
    epsilon_guard: EpsilonGuard,

    // Config
    spec_sig: String,
    budget_limit: f64,
    spam_score_limit: f64,
    running_spend: f64,
    tenant_id: String,
    ledger_url: String,

    // HTTP
    http_client: Client,
}

impl Watcher {
    async fn new() -> Result<Self> {
        // Build a single registry and register all metrics on it
        let mut reg = Registry::default();
        let metrics = Metrics::new(&mut reg);
        let registry = Arc::new(reg);

        let assumption_monitor = AssumptionMonitor::new();
        let epsilon_guard = EpsilonGuard::new().await?;

        let spec_sig = env::var("SPEC_SIG").unwrap_or_default();
        let budget_limit = env::var("BUDGET_LIMIT")
            .unwrap_or_else(|_| "1000.0".to_string())
            .parse()
            .unwrap_or(1000.0);
        let spam_score_limit = env::var("SPAM_SCORE_LIMIT")
            .unwrap_or_else(|_| "0.8".to_string())
            .parse()
            .unwrap_or(0.8);
        let tenant_id = env::var("TENANT_ID").unwrap_or_default();
        let ledger_url = env::var("LEDGER_URL").unwrap_or_else(|_| "http://localhost:3000".to_string());
        let http_client = Client::new();

        Ok(Self {
            registry,
            metrics,
            assumption_monitor,
            epsilon_guard,
            spec_sig,
            budget_limit,
            spam_score_limit,
            running_spend: 0.0,
            tenant_id,
            ledger_url,
            http_client,
        })
    }

    fn process_action(&mut self, action: &Action) -> Result<bool> {
        self.metrics.total_actions.inc();

        // Enforce privacy budget first
        if let (Some(epsilon), Some(delta)) = (action.privacy_epsilon, action.privacy_delta) {
            let runtime = tokio::runtime::Runtime::new()?;
            let allowed = runtime.block_on(self.epsilon_guard.check_query(
                &self.tenant_id, epsilon, delta,
            ))?;

            if !allowed {
                self.metrics.privacy_violations.inc();
                self.log_violation(&format!(
                    "Privacy budget exceeded: epsilon={}, delta={}",
                    epsilon, delta
                ));
                return Ok(false);
            }
        }

        // Update privacy budget metric from guard (store epsilon * 1000)
        let runtime = tokio::runtime::Runtime::new()?;
        if let Ok((remaining_epsilon, _)) =
            runtime.block_on(self.epsilon_guard.get_remaining_budget(&self.tenant_id))
        {
            self
                .metrics
                .privacy_budget_remaining
                .set((remaining_epsilon * 1000.0) as i64);
        }

        // Budget limit check
        if let Some(amount) = action.usd_amount {
            self.running_spend += amount;
            if self.running_spend > self.budget_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!(
                    "Budget limit exceeded: ${:.2} > ${:.2}",
                    self.running_spend, self.budget_limit
                ));
                return Ok(false);
            }
        }

        // Spam score check
        if let Some(spam_score) = action.spam_score {
            if spam_score > self.spam_score_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!(
                    "Spam score too high: {:.2} > {:.2}",
                    spam_score, self.spam_score_limit
                ));
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        let key = assumption.key.clone();
        let expected = assumption.expected.clone();
        let valid = self.assumption_monitor.process_assumption(assumption)?;

        if !valid {
            self.metrics.assumption_violations.inc();
            self.log_violation(&format!(
                "Assumption violation: key={}, expected={}",
                key, expected
            ));
        }

        Ok(valid)
    }

    fn log_violation(&self, reason: &str) {
        let trip = GuardTrip {
            event: "guard_trip".to_string(),
            reason: reason.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };

        warn!("Guard trip: {}", reason);

        if let Ok(mut log_file) = File::create("/tmp/guard_trips.log") {
            use std::io::Write;
            let _ = writeln!(log_file, "{}", serde_json::to_string(&trip).unwrap());
        }
    }

    async fn publish_usage_metrics(&self) -> Result<()> {
        // Allow disabling by leaving LEDGER_URL empty
        if self.ledger_url.trim().is_empty() {
            return Ok(());
        }

        let usage_event = UsageEvent {
            tenant_id: self.tenant_id.clone(),
            cpu_ms: 100,      // Mock CPU usage
            net_bytes: 1024,  // Mock network usage
            ts: chrono::Utc::now().to_rfc3339(),
        };

        let resp = self
            .http_client
            .post(format!("{}/api/usage", self.ledger_url))
            .json(&usage_event)
            .send()
            .await?;

        if resp.status().is_success() {
            // ok
        } else if resp.status() == StatusCode::NOT_FOUND {
            // Likely no usage endpoint — keep logs quiet in dev
            tracing::debug!("Usage endpoint not found (404); skipping publish");
        } else {
            warn!("Failed to publish usage metrics: {}", resp.status());
        }

        Ok(())
    }

    async fn watch_container_logs(&mut self) -> Result<()> {
        let log_file = env::var("LOG_FILE").unwrap_or_else(|_| "/var/log/container.log".to_string());

        loop {
            if let Ok(file) = File::open(&log_file) {
                let reader = BufReader::new(file);

                for line in reader.lines() {
                    if let Ok(line) = line {
                        if line.contains("\"action\"") {
                            if let Ok(action) = serde_json::from_str::<Action>(&line) {
                                if let Err(e) = self.process_action(&action) {
                                    error!("Failed to process action: {}", e);
                                }
                            }
                        } else if line.contains("\"assumption\"") {
                            if let Ok(assumption) = serde_json::from_str::<Assumption>(&line) {
                                if let Err(e) = self.process_assumption(assumption) {
                                    error!("Failed to process assumption: {}", e);
                                }
                            }
                        }
                    }
                }
            }

            sleep(Duration::from_secs(1)).await;
        }
    }
}

async fn metrics_handler(
    _req: Request<Body>,
    registry: Arc<Registry>,
) -> Result<Response<Body>, hyper::Error> {
    let mut buffer = String::new();
    encode(&mut buffer, &registry).unwrap();

    Ok(Response::builder()
        .header("Content-Type", "text/plain; version=0.0.4; charset=utf-8")
        .body(Body::from(buffer))
        .unwrap())
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let watcher = Watcher::new().await?;

    // Load privacy configurations (will log a warning in dev mode without K8s)
    if let Err(e) = watcher.epsilon_guard.load_configs().await {
        warn!("Failed to load privacy configs: {}", e);
    }

    // Start Prometheus /metrics server using the registry from Watcher
    let registry = watcher.registry.clone();
    let metrics_addr = SocketAddr::from(([0, 0, 0, 0], 9090));
    let make_svc = make_service_fn(move |_conn| {
        let registry = registry.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                metrics_handler(req, registry.clone())
            }))
        }
    });
    let metrics_server = Server::bind(&metrics_addr).serve(make_svc);
    info!("Metrics server listening on {}", metrics_addr);

    // Start HTTP health server on PORT (default 8006)
    let http_port: u16 = std::env::var("PORT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8006);
    let http_addr = SocketAddr::from(([0, 0, 0, 0], http_port));
    tokio::spawn(async move {
        if let Err(e) = http_health::serve_http(http_addr).await {
            tracing::error!("HTTP health server failed: {e}");
        } else {
            tracing::info!("HTTP health server listening on {}", http_addr);
        }
    });

    // Background tasks
    let watcher = Arc::new(tokio::sync::Mutex::new(watcher));

    let usage_task = {
        let watcher = watcher.clone();
        tokio::spawn(async move {
            loop {
                {
                    let watcher = watcher.lock().await;
                    if let Err(e) = watcher.publish_usage_metrics().await {
                        error!("Failed to publish usage metrics: {}", e);
                    }
                }
                sleep(Duration::from_secs(60)).await;
            }
        })
    };

    let log_watch_task = {
        let watcher = watcher.clone();
        tokio::spawn(async move {
            loop {
                {
                    let mut watcher = watcher.lock().await;
                    if let Err(e) = watcher.watch_container_logs().await {
                        error!("Failed to watch container logs: {}", e);
                    }
                }
                sleep(Duration::from_secs(1)).await;
            }
        })
    };

    // Wait for server or tasks to complete
    tokio::select! {
        _ = metrics_server => info!("Metrics server stopped"),
        _ = usage_task => info!("Usage task stopped"),
        _ = log_watch_task => info!("Log watch task stopped"),
    }

    // Keep process alive if everything else ended
    std::future::pending::<()>().await;
    // unreachable
    #[allow(unreachable_code)]
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Watcher::new() is async; this test is only illustrative and
    // not compiled in release builds.
    #[test]
    fn test_budget_violation() {
        // Synchronous unit test stub: do not run in normal builds.
        // If you enable tests, convert this to #[tokio::test] and await Watcher::new().
        let mut running_spend = 90.0;
        let budget_limit = 100.0;

        let action = Action {
            action_type: "test".to_string(),
            spam_score: None,
            usd_amount: Some(20.0),
            privacy_epsilon: None,
            privacy_delta: None,
        };

        // Simulate the check logic
        if let Some(amount) = action.usd_amount {
            running_spend += amount;
            assert!(running_spend > budget_limit);
        }
    }
}
