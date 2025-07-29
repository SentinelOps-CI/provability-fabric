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

struct Metrics {
    total_actions: Counter,
    violations: Counter,
    assumption_violations: Counter,
}

impl Metrics {
    fn new(registry: &mut Registry) -> Self {
        let total_actions = Counter::default();
        let violations = Counter::default();
        let assumption_violations = Counter::default();

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

        Self {
            total_actions,
            violations,
            assumption_violations,
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
}

impl Watcher {
    fn new() -> Result<Self> {
        let spec_sig = env::var("SPEC_SIG")
            .context("SPEC_SIG environment variable not set")?;
        
        let budget_limit = env::var("LIMIT_BUDGET")
            .unwrap_or_else(|_| "300.0".to_string())
            .parse::<f64>()
            .context("Invalid LIMIT_BUDGET value")?;
        
        let spam_score_limit = env::var("LIMIT_SPAMSCORE")
            .unwrap_or_else(|_| "0.07".to_string())
            .parse::<f64>()
            .context("Invalid LIMIT_SPAMSCORE value")?;

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
        })
    }

    fn process_action(&mut self, action: &Action) -> Result<bool> {
        self.metrics.total_actions.inc();

        // Check spam score
        if let Some(score) = action.spam_score {
            if score > self.spam_score_limit {
                self.metrics.violations.inc();
                return Ok(false);
            }
        }

        // Check budget
        if let Some(amount) = action.usd_amount {
            self.running_spend += amount;
            if self.running_spend > self.budget_limit {
                self.metrics.violations.inc();
                return Ok(false);
            }
        }

        Ok(true)
    }

    fn process_assumption(&mut self, assumption: Assumption) -> Result<bool> {
        let result = self.assumption_monitor.process_assumption(assumption)?;
        
        if !result {
            self.metrics.assumption_violations.inc();
        }
        
        Ok(result)
    }

    fn log_violation(&self, reason: &str) {
        let trip = GuardTrip {
            event: "guard_trip".to_string(),
            reason: reason.to_string(),
            timestamp: chrono::Utc::now().to_rfc3339(),
        };

        if let Ok(json) = serde_json::to_string(&trip) {
            eprintln!("{}", json);
        }
    }

    async fn watch_container_logs(&mut self) -> Result<()> {
        let log_path = "/proc/1/fd/1";
        
        loop {
            if let Ok(file) = File::open(log_path) {
                let reader = BufReader::new(file);
                
                for line in reader.lines() {
                    if let Ok(line) = line {
                        // Process action messages
                        if line.contains("\"action\":") {
                            if let Ok(action) = serde_json::from_str::<Action>(&line) {
                                if !self.process_action(&action)? {
                                    let reason = if action.spam_score.unwrap_or(0.0) > self.spam_score_limit {
                                        "spam_score_exceeded"
                                    } else {
                                        "budget_exceeded"
                                    };
                                    
                                    self.log_violation(reason);
                                    std::process::exit(1);
                                }
                            }
                        }
                        
                        // Process assumption messages
                        if line.contains("\"assumption\":") {
                            if let Ok(assumption) = serde_json::from_str::<Assumption>(&line) {
                                if !self.process_assumption(assumption)? {
                                    self.log_violation("assumption_drift");
                                    std::process::exit(1);
                                }
                            }
                        }
                    }
                }
            }
            
            sleep(Duration::from_millis(100)).await;
        }
    }
}

async fn metrics_handler(
    req: Request<Body>,
    registry: Arc<Registry>,
) -> Result<Response<Body>, hyper::Error> {
    let mut buffer = Vec::new();
    encode(&mut buffer, &registry).unwrap();
    
    Ok(Response::builder()
        .header("Content-Type", "application/openmetrics-text; version=1.0.0; charset=utf-8")
        .body(Body::from(buffer))
        .unwrap())
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    info!("Starting sidecar watcher...");
    
    let mut watcher = Watcher::new()?;
    info!("Watcher initialized with spec_sig: {}", watcher.spec_sig);
    
    // Start metrics server
    let registry = Arc::new(Registry::default());
    let metrics_registry = registry.clone();
    
    let addr = SocketAddr::from(([0, 0, 0, 0], 9102));
    let make_svc = make_service_fn(move |_conn| {
        let registry = metrics_registry.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let registry = registry.clone();
                async move { metrics_handler(req, registry).await }
            }))
        }
    });
    
    let server = Server::bind(&addr).serve(make_svc);
    info!("Metrics server listening on {}", addr);
    
    // Start watching logs
    tokio::spawn(async move {
        if let Err(e) = watcher.watch_container_logs().await {
            error!("Error watching logs: {}", e);
            std::process::exit(1);
        }
    });
    
    if let Err(e) = server.await {
        error!("Server error: {}", e);
    }
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;

    #[test]
    fn test_budget_violation() {
        env::set_var("SPEC_SIG", "test-sig");
        env::set_var("LIMIT_BUDGET", "100.0");
        env::set_var("LIMIT_SPAMSCORE", "0.07");
        
        let mut watcher = Watcher::new().unwrap();
        
        // Add actions that exceed budget
        let action1 = Action {
            action_type: "LogSpend".to_string(),
            spam_score: None,
            usd_amount: Some(60.0),
        };
        
        let action2 = Action {
            action_type: "LogSpend".to_string(),
            spam_score: None,
            usd_amount: Some(50.0),
        };
        
        assert!(watcher.process_action(&action1).unwrap());
        assert!(!watcher.process_action(&action2).unwrap()); // Should violate budget
    }
} 