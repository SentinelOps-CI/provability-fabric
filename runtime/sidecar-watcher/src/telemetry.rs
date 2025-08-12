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
    client: Option<reqwest::Client>,
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
        // Create optimized HTTP client with connection pooling
        let client = reqwest::Client::builder()
            .pool_max_idle_per_host(10) // Optimize for typical load
            .pool_idle_timeout(Duration::from_secs(90)) // Keep connections alive
            .http2_prior_knowledge() // Force HTTP/2 for better performance
            .timeout(Duration::from_secs(30)) // Request timeout
            .connect_timeout(Duration::from_secs(10)) // Connection timeout
            .tcp_keepalive(Some(Duration::from_secs(30))) // TCP keepalive
            .build()
            .expect("Failed to create HTTP client");

        Self {
            client: Some(client),
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
        let start_time = std::time::Instant::now();
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

        // Use the optimized client from the struct
        let client = self.client.as_ref().expect("Client not initialized");
        
        // Record connection reuse metrics
        let pool_status = client.get_pool_status();
        gauge!("http_connection_pool_size", pool_status.idle_connections as f64);
        gauge!("http_connection_pool_available", pool_status.available_connections as f64);
        
        let response = client
            .post(&format!("{}/heartbeat", self.attestor_url))
            .json(&heartbeat)
            .send()
            .await?;

        let latency = start_time.elapsed();
        histogram!("http_request_duration_seconds", latency.as_secs_f64());
        
        if !response.status().is_success() {
            counter!("http_requests_failed_total", 1);
            return Err(format!("Heartbeat failed: {}", response.status()).into());
        }

        counter!("http_requests_success_total", 1);
        counter!("heartbeat_sent_total", 1);
        
        Ok(())
    }

    pub async fn send_terminate(&self, reason: String) -> Result<(), Box<dyn std::error::Error>> {
        let start_time = std::time::Instant::now();
        let terminate = TerminateFrame {
            capsule_hash: self.capsule_hash.clone(),
            timestamp: chrono::Utc::now().timestamp(),
            reason,
        };

        let client = self.client.as_ref().expect("Client not initialized");
        
        let response = client
            .post(&format!("{}/terminate", self.attestor_url))
            .json(&terminate)
            .send()
            .await?;

        let latency = start_time.elapsed();
        histogram!("http_request_duration_seconds", latency.as_secs_f64());

        if !response.status().is_success() {
            counter!("http_requests_failed_total", 1);
            return Err(format!("Terminate failed: {}", response.status()).into());
        }

        counter!("http_requests_success_total", 1);
        counter!("terminate_sent_total", 1);
        
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