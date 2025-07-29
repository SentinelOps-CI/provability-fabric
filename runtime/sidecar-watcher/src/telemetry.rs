use tonic::{transport::Channel, Request};
use tokio::time::{interval, Duration};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;

use crate::assumption::AssumptionMonitor;

#[derive(Debug, Serialize, Deserialize)]
pub struct Heartbeat {
    pub capsule_hash: String,
    pub timestamp: i64,
    pub metrics: HeartbeatMetrics,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct HeartbeatMetrics {
    pub total_actions: u64,
    pub violations: u64,
    pub assumption_violations: u64,
    pub running_spend: f64,
    pub budget_limit: f64,
    pub spam_score_limit: f64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct TerminateFrame {
    pub capsule_hash: String,
    pub timestamp: i64,
    pub reason: String,
}

pub struct TelemetryClient {
    client: Option<tonic::transport::Channel>,
    attestor_url: String,
    capsule_hash: String,
    assumption_monitor: Arc<Mutex<AssumptionMonitor>>,
    metrics: Arc<Mutex<HeartbeatMetrics>>,
}

impl TelemetryClient {
    pub fn new(
        attestor_url: String,
        capsule_hash: String,
        assumption_monitor: Arc<Mutex<AssumptionMonitor>>,
        metrics: Arc<Mutex<HeartbeatMetrics>>,
    ) -> Self {
        Self {
            client: None,
            attestor_url,
            capsule_hash,
            assumption_monitor,
            metrics,
        }
    }

    pub async fn connect(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let channel = tonic::transport::Channel::from_shared(self.attestor_url.clone())?
            .connect()
            .await?;
        
        self.client = Some(channel);
        Ok(())
    }

    pub async fn start_heartbeat(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = interval(Duration::from_secs(5));
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.send_heartbeat().await {
                eprintln!("Failed to send heartbeat: {}", e);
                // Try to reconnect
                self.connect().await?;
            }
        }
    }

    async fn send_heartbeat(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        let metrics = self.metrics.lock().await;
        let assumption_monitor = self.assumption_monitor.lock().await;
        
        let heartbeat = Heartbeat {
            capsule_hash: self.capsule_hash.clone(),
            timestamp: chrono::Utc::now().timestamp(),
            metrics: HeartbeatMetrics {
                total_actions: metrics.total_actions,
                violations: metrics.violations,
                assumption_violations: assumption_monitor.violation_count(),
                running_spend: metrics.running_spend,
                budget_limit: metrics.budget_limit,
                spam_score_limit: metrics.spam_score_limit,
            },
        };

        // For now, we'll use HTTP since we haven't defined the gRPC proto
        // In a real implementation, this would be a gRPC stream
        let client = reqwest::Client::new();
        let response = client
            .post(&format!("{}/heartbeat", self.attestor_url))
            .json(&heartbeat)
            .send()
            .await?;

        if !response.status().is_success() {
            return Err(format!("Heartbeat failed: {}", response.status()).into());
        }

        Ok(())
    }

    pub async fn send_terminate(&self, reason: String) -> Result<(), Box<dyn std::error::Error>> {
        let terminate = TerminateFrame {
            capsule_hash: self.capsule_hash.clone(),
            timestamp: chrono::Utc::now().timestamp(),
            reason,
        };

        let client = reqwest::Client::new();
        let response = client
            .post(&format!("{}/terminate", self.attestor_url))
            .json(&terminate)
            .send()
            .await?;

        if !response.status().is_success() {
            return Err(format!("Terminate failed: {}", response.status()).into());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assumption::AssumptionMonitor;

    #[tokio::test]
    async fn test_telemetry_client_creation() {
        let assumption_monitor = Arc::new(Mutex::new(AssumptionMonitor::new()));
        let metrics = Arc::new(Mutex::new(HeartbeatMetrics {
            total_actions: 0,
            violations: 0,
            assumption_violations: 0,
            running_spend: 0.0,
            budget_limit: 100.0,
            spam_score_limit: 0.5,
        }));

        let client = TelemetryClient::new(
            "http://localhost:8080".to_string(),
            "test-capsule-hash".to_string(),
            assumption_monitor,
            metrics,
        );

        assert_eq!(client.capsule_hash, "test-capsule-hash");
        assert_eq!(client.attestor_url, "http://localhost:8080");
    }
}