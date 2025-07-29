// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use prometheus_client::{
    encoding::text::encode,
    metrics::{counter::Counter, family::Family, gauge::Gauge},
    registry::Registry,
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    env,
    fs::File,
    io::{BufRead, BufReader},
    net::SocketAddr,
    sync::Arc,
    time::Duration,
};
use tokio::time::sleep;
use tracing::{error, info, warn};
use reqwest::Client;

mod assumption;

use assumption::{Assumption, AssumptionMonitor};

// Import epsilon guard
mod privacy;
use privacy::epsilon_guard::{EpsilonGuard, PrivacyMetrics};

#[derive(Debug, Deserialize, Serialize)]
struct Action {
    #[serde(rename = "action")]
    action_type: String,
    spam_score: Option<f64>,
    usd_amount: Option<f64>,
    privacy_epsilon: Option<f64>, // New field for privacy budget
    privacy_delta: Option<f64>,   // New field for privacy budget
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
    privacy_budget_remaining: Gauge<f64>, // New privacy metric
    privacy_violations: Counter,          // New privacy violation counter
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
            Box::new(total_actions.clone()),
        );
        registry.register(
            "violations",
            "Total number of constraint violations",
            Box::new(violations.clone()),
        );
        registry.register(
            "assumption_violations_total",
            "Total number of assumption violations",
            Box::new(assumption_violations.clone()),
        );
        registry.register(
            "cpu_usage_ms",
            "Total CPU usage in milliseconds",
            Box::new(cpu_usage_ms.clone()),
        );
        registry.register(
            "network_bytes",
            "Total network bytes transferred",
            Box::new(network_bytes.clone()),
        );
        registry.register(
            "privacy_budget_remaining",
            "Remaining privacy budget (epsilon)",
            Box::new(privacy_budget_remaining.clone()),
        );
        registry.register(
            "privacy_violations_total",
            "Total number of privacy budget violations",
            Box::new(privacy_violations.clone()),
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
    metrics: Metrics,
    assumption_monitor: AssumptionMonitor,
    epsilon_guard: EpsilonGuard, // New epsilon guard
    spec_sig: String,
    budget_limit: f64,
    spam_score_limit: f64,
    running_spend: f64,
    tenant_id: String,
    ledger_url: String,
    http_client: Client,
}

impl Watcher {
    fn new() -> Result<Self> {
        let mut registry = Registry::default();
        let metrics = Metrics::new(&mut registry);
        
        let assumption_monitor = AssumptionMonitor::new()?;
        let epsilon_guard = EpsilonGuard::new()?; // Initialize epsilon guard
        
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
        
        // Check privacy budget first
        if let (Some(epsilon), Some(delta)) = (action.privacy_epsilon, action.privacy_delta) {
            // Use tokio runtime to call async function
            let runtime = tokio::runtime::Runtime::new()?;
            let allowed = runtime.block_on(self.epsilon_guard.check_query(
                &self.tenant_id, epsilon, delta
            ))?;
            
            if !allowed {
                self.metrics.privacy_violations.inc();
                self.log_violation(&format!("Privacy budget exceeded: epsilon={}, delta={}", epsilon, delta));
                return Ok(false);
            }
        }
        
        // Update privacy budget metric
        let runtime = tokio::runtime::Runtime::new()?;
        if let Ok((remaining_epsilon, _)) = runtime.block_on(self.epsilon_guard.get_remaining_budget(&self.tenant_id)) {
            self.metrics.privacy_budget_remaining.set(remaining_epsilon);
        }
        
        // Existing budget and spam checks
        if let Some(amount) = action.usd_amount {
            self.running_spend += amount;
            if self.running_spend > self.budget_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!("Budget limit exceeded: ${:.2} > ${:.2}", self.running_spend, self.budget_limit));
                return Ok(false);
            }
        }
        
        if let Some(spam_score) = action.spam_score {
            if spam_score > self.spam_score_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!("Spam score too high: {:.2} > {:.2}", spam_score, self.spam_score_limit));
                return Ok(false);
            }
        }
        
        Ok(true)
    }

    fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        let valid = self.assumption_monitor.check_assumption(&assumption)?;
        
        if !valid {
            self.metrics.assumption_violations.inc();
            self.log_violation(&format!("Assumption violation: {}", assumption.reason));
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
        
        // Log to file or send to monitoring system
        if let Ok(log_file) = File::create("/tmp/guard_trips.log") {
            use std::io::Write;
            let _ = writeln!(log_file, "{}", serde_json::to_string(&trip).unwrap());
        }
    }

    async fn publish_usage_metrics(&self) -> Result<()> {
        let usage_event = UsageEvent {
            tenant_id: self.tenant_id.clone(),
            cpu_ms: 100, // Mock CPU usage
            net_bytes: 1024, // Mock network usage
            ts: chrono::Utc::now().to_rfc3339(),
        };
        
        let response = self.http_client
            .post(&format!("{}/api/usage", self.ledger_url))
            .json(&usage_event)
            .send()
            .await?;
            
        if !response.status().is_success() {
            warn!("Failed to publish usage metrics: {}", response.status());
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
    req: Request<Body>,
    registry: Arc<Registry>,
) -> Result<Response<Body>, hyper::Error> {
    let mut buffer = vec![];
    encode(&mut buffer, &registry).unwrap();
    
    Ok(Response::builder()
        .header("Content-Type", "text/plain; version=0.0.4; charset=utf-8")
        .body(Body::from(buffer))
        .unwrap())
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    let mut watcher = Watcher::new()?;
    
    // Load privacy configurations
    if let Err(e) = watcher.epsilon_guard.load_configs().await {
        warn!("Failed to load privacy configs: {}", e);
    }
    
    // Start metrics server
    let registry = Arc::new(Registry::default());
    let addr = SocketAddr::from(([0, 0, 0, 0], 9090));
    
    let make_svc = make_service_fn(move |_conn| {
        let registry = registry.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                metrics_handler(req, registry.clone())
            }))
        }
    });
    
    let server = Server::bind(&addr).serve(make_svc);
    info!("Metrics server listening on {}", addr);
    
    // Start background tasks
    let watcher_clone = Arc::new(tokio::sync::Mutex::new(watcher));
    
    let usage_task = {
        let watcher = watcher_clone.clone();
        tokio::spawn(async move {
            loop {
                if let Ok(mut watcher) = watcher.lock().await {
                    if let Err(e) = watcher.publish_usage_metrics().await {
                        error!("Failed to publish usage metrics: {}", e);
                    }
                }
                sleep(Duration::from_secs(60)).await;
            }
        })
    };
    
    let log_watch_task = {
        let watcher = watcher_clone.clone();
        tokio::spawn(async move {
            loop {
                if let Ok(mut watcher) = watcher.lock().await {
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
        _ = server => info!("Metrics server stopped"),
        _ = usage_task => info!("Usage task stopped"),
        _ = log_watch_task => info!("Log watch task stopped"),
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_budget_violation() {
        let mut watcher = Watcher::new().unwrap();
        watcher.budget_limit = 100.0;
        watcher.running_spend = 90.0;
        
        let action = Action {
            action_type: "test".to_string(),
            spam_score: None,
            usd_amount: Some(20.0),
            privacy_epsilon: None,
            privacy_delta: None,
        };
        
        assert!(!watcher.process_action(&action).unwrap());
    }
} 