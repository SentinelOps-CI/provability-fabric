// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use prometheus_client::{
    encoding::text::encode,
    metrics::{counter::Counter, family::Family},
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

#[derive(Debug, Deserialize, Serialize)]
struct Action {
    #[serde(rename = "action")]
    action_type: String,
    spam_score: Option<f64>,
    usd_amount: Option<f64>,
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
}

impl Metrics {
    fn new(registry: &mut Registry) -> Self {
        let total_actions = Counter::default();
        let violations = Counter::default();
        let assumption_violations = Counter::default();
        let cpu_usage_ms = Counter::default();
        let network_bytes = Counter::default();

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

        Self {
            total_actions,
            violations,
            assumption_violations,
            cpu_usage_ms,
            network_bytes,
        }
    }
}

struct Watcher {
    metrics: Metrics,
    assumption_monitor: AssumptionMonitor,
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
        let spec_sig = env::var("SPEC_SIG")
            .context("SPEC_SIG environment variable not set")?;
        
        let budget_limit = env::var("LIMIT_BUDGET")
            .unwrap_or_else(|_| "300.0".to_string())
            .parse::<f64>()
            .context("Invalid LIMIT_BUDGET value")?;
        
        let spam_score_limit = env::var("LIMIT_SPAM_SCORE")
            .unwrap_or_else(|_| "0.8".to_string())
            .parse::<f64>()
            .context("Invalid LIMIT_SPAM_SCORE value")?;
        
        let tenant_id = env::var("TENANT_ID")
            .context("TENANT_ID environment variable not set")?;
        
        let ledger_url = env::var("LEDGER_URL")
            .unwrap_or_else(|_| "http://localhost:4000".to_string());
        
        let http_client = Client::new();

        let mut registry = Registry::default();
        let metrics = Metrics::new(&mut registry);
        let assumption_monitor = AssumptionMonitor::new();

        Ok(Self {
            metrics,
            assumption_monitor,
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
        
        // Track CPU usage (simplified - in real implementation would get from cgroups)
        let cpu_ms = 100; // Simplified - would be actual CPU time
        self.metrics.cpu_usage_ms.inc_by(cpu_ms);
        
        // Track network usage (simplified)
        let net_bytes = 1024; // Simplified - would be actual network bytes
        self.metrics.network_bytes.inc_by(net_bytes);

        // Check spam score
        if let Some(spam_score) = action.spam_score {
            if spam_score > self.spam_score_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!("Spam score {} exceeds limit {}", spam_score, self.spam_score_limit));
                return Ok(false);
            }
        }

        // Check budget
        if let Some(amount) = action.usd_amount {
            self.running_spend += amount;
            if self.running_spend > self.budget_limit {
                self.metrics.violations.inc();
                self.log_violation(&format!("Budget limit {} exceeded: {}", self.budget_limit, self.running_spend));
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        match self.assumption_monitor.process_assumption(assumption) {
            Ok(violated) => {
                if violated {
                    self.metrics.assumption_violations.inc();
                    self.log_violation("Assumption violation detected");
                    return Ok(false);
                }
                Ok(true)
            }
            Err(e) => {
                error!("Error processing assumption: {}", e);
                Ok(false)
            }
        }
    }

    fn log_violation(&self, reason: &str) {
        let trip = GuardTrip {
            event: "constraint_violation".to_string(),
            reason: reason.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };
        
        if let Ok(json) = serde_json::to_string(&trip) {
            eprintln!("VIOLATION: {}", json);
        }
    }

    async fn publish_usage_metrics(&self) -> Result<()> {
        let usage_event = UsageEvent {
            tenant_id: self.tenant_id.clone(),
            cpu_ms: self.metrics.cpu_usage_ms.get(),
            net_bytes: self.metrics.network_bytes.get(),
            ts: chrono::Utc::now().to_rfc3339(),
        };

        let url = format!("{}/usage", self.ledger_url);
        
        match self.http_client
            .post(&url)
            .json(&usage_event)
            .send()
            .await
        {
            Ok(response) => {
                if response.status().is_success() {
                    info!("Usage metrics published successfully");
                } else {
                    warn!("Failed to publish usage metrics: {}", response.status());
                }
            }
            Err(e) => {
                warn!("Error publishing usage metrics: {}", e);
            }
        }

        Ok(())
    }

    async fn watch_container_logs(&mut self) -> Result<()> {
        let log_file = env::var("LOG_FILE").unwrap_or_else(|_| "/dev/stdin".to_string());
        
        info!("Starting to watch logs from: {}", log_file);
        
        let file = File::open(&log_file)?;
        let reader = BufReader::new(file);
        let mut lines = reader.lines();
        
        let mut last_usage_publish = std::time::Instant::now();
        let usage_publish_interval = Duration::from_secs(60); // Publish every 60 seconds

        while let Some(line) = lines.next() {
            let line = line?;
            
            // Try to parse as JSON action
            if let Ok(action) = serde_json::from_str::<Action>(&line) {
                if !self.process_action(&action)? {
                    return Ok(());
                }
            }
            
            // Try to parse as assumption
            if let Ok(assumption) = serde_json::from_str::<Assumption>(&line) {
                if !self.process_assumption(assumption)? {
                    return Ok(());
                }
            }
            
            // Check if it's time to publish usage metrics
            if last_usage_publish.elapsed() >= usage_publish_interval {
                if let Err(e) = self.publish_usage_metrics().await {
                    warn!("Failed to publish usage metrics: {}", e);
                }
                last_usage_publish = std::time::Instant::now();
            }
        }
        
        Ok(())
    }
}

async fn metrics_handler(
    req: Request<Body>,
    registry: Arc<Registry>,
) -> Result<Response<Body>, hyper::Error> {
    if req.uri().path() == "/metrics" {
        let mut buffer = Vec::new();
        encode(&mut buffer, &registry).unwrap();
        
        Ok(Response::builder()
            .header("Content-Type", "application/openmetrics-text; version=1.0.0; charset=utf-8")
            .body(Body::from(buffer))
            .unwrap())
    } else {
        Ok(Response::builder()
            .status(404)
            .body(Body::from("Not Found"))
            .unwrap())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    let watcher = Watcher::new()?;
    let addr = SocketAddr::from(([0, 0, 0, 0], 9090));
    
    info!("Starting sidecar watcher on {}", addr);
    
    // Start metrics server
    let registry = Arc::new(Registry::default());
    let registry_clone = registry.clone();
    
    let make_svc = make_service_fn(move |_conn| {
        let registry = registry_clone.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                metrics_handler(req, registry.clone())
            }))
        }
    });
    
    let server = Server::bind(&addr).serve(make_svc);
    
    // Start log watching in a separate task
    let mut watcher_clone = watcher;
    let watch_task = tokio::spawn(async move {
        if let Err(e) = watcher_clone.watch_container_logs().await {
            error!("Error watching logs: {}", e);
        }
    });
    
    // Run both the metrics server and log watching
    tokio::select! {
        _ = server => {
            info!("Metrics server stopped");
        }
        _ = watch_task => {
            info!("Log watching stopped");
        }
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
        };
        
        assert!(!watcher.process_action(&action).unwrap());
    }
} 