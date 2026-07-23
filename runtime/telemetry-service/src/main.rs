// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::Result;
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use tokio::time::interval;
use tracing::{error, info};
use reqwest::Client;
use prometheus_client::{
    encoding::text::encode,
    registry::Registry,
};

#[derive(Debug, Clone, Deserialize, Serialize)]
struct TelemetryData {
    // Time-to-first-cert metrics
    time_to_first_cert_samples: Vec<f64>,
    
    // Replay pass rate metrics
    replay_total_tests: u64,
    replay_passed_tests: u64,
    
    // P95 latency metrics
    latency_samples: Vec<f64>,
    
    // Certificate issuance metrics
    cert_issuance_total: u64,
    cert_issuance_failures: u64,
    
    // Metadata (no PII)
    tenant_id_hash: String,  // Hashed tenant ID for aggregation
    timestamp: i64,
    version: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct TelemetryResponse {
    success: bool,
    message: String,
    aggregated_data: Option<AggregatedTelemetry>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct AggregatedTelemetry {
    avg_time_to_first_cert: f64,
    replay_pass_rate: f64,
    p95_latency: f64,
    cert_success_rate: f64,
    sample_count: u64,
    aggregation_period_hours: u64,
}

struct TelemetryService {
    // Aggregated metrics (no PII)
    aggregated_metrics: Arc<RwLock<AggregatedTelemetry>>,
    
    // Raw telemetry data (stored temporarily for aggregation)
    raw_telemetry: Arc<RwLock<Vec<TelemetryData>>>,
    
    // Prometheus metrics registry
    registry: Arc<Registry>,
    
    // HTTP client for external services
    http_client: Client,
    
    // Configuration
    aggregation_interval_hours: u64,
    data_retention_hours: u64,
    opt_in_enabled: bool,
}

impl TelemetryService {
    fn new() -> Self {
        let registry = Registry::default();
        
        // Initialize aggregated metrics
        let aggregated_metrics = Arc::new(RwLock::new(AggregatedTelemetry {
            avg_time_to_first_cert: 0.0,
            replay_pass_rate: 0.0,
            p95_latency: 0.0,
            cert_success_rate: 0.0,
            sample_count: 0,
            aggregation_period_hours: 24,
        }));

        Self {
            aggregated_metrics,
            raw_telemetry: Arc::new(RwLock::new(Vec::new())),
            registry: Arc::new(registry),
            http_client: Client::new(),
            aggregation_interval_hours: std::env::var("AGGREGATION_INTERVAL_HOURS")
                .unwrap_or_else(|_| "1".to_string())
                .parse()
                .unwrap_or(1),
            data_retention_hours: std::env::var("DATA_RETENTION_HOURS")
                .unwrap_or_else(|_| "168".to_string()) // 7 days
                .parse()
                .unwrap_or(168),
            opt_in_enabled: std::env::var("TELEMETRY_OPT_IN_ENABLED")
                .unwrap_or_else(|_| "true".to_string())
                .parse()
                .unwrap_or(true),
        }
    }

    async fn collect_telemetry(&self, data: TelemetryData) -> Result<TelemetryResponse> {
        // Check if telemetry is opt-in and enabled
        if !self.opt_in_enabled {
            return Ok(TelemetryResponse {
                success: false,
                message: "Telemetry collection is disabled".to_string(),
                aggregated_data: None,
            });
        }

        // Validate telemetry data (ensure no PII)
        self.validate_telemetry_data(&data)?;

        // Store raw telemetry data
        {
            let mut raw_data = self.raw_telemetry.write().await;
            raw_data.push(data);
            
            // Clean up old data
            self.cleanup_old_data(&mut raw_data).await;
        }

        // Get current aggregated metrics
        let aggregated = (*self.aggregated_metrics.read().await).clone();

        Ok(TelemetryResponse {
            success: true,
            message: "Telemetry data collected successfully".to_string(),
            aggregated_data: Some(aggregated),
        })
    }

    fn validate_telemetry_data(&self, data: &TelemetryData) -> Result<()> {
        // Ensure no PII is included in telemetry data
        if data.tenant_id_hash.len() < 32 {
            return Err(anyhow::anyhow!("Tenant ID must be hashed (minimum 32 characters)"));
        }

        // Validate data ranges
        if data.time_to_first_cert_samples.iter().any(|&x| !(0.0..=3600.0).contains(&x)) {
            return Err(anyhow::anyhow!("Invalid time-to-first-cert samples"));
        }

        if data.latency_samples.iter().any(|&x| !(0.0..=3600.0).contains(&x)) {
            return Err(anyhow::anyhow!("Invalid latency samples"));
        }

        Ok(())
    }

    async fn cleanup_old_data(&self, raw_data: &mut Vec<TelemetryData>) {
        let cutoff_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64
            - (self.data_retention_hours * 3600) as i64;

        raw_data.retain(|data| data.timestamp > cutoff_time);
    }

    async fn aggregate_telemetry(&self) -> Result<()> {
        let raw_data = (*self.raw_telemetry.read().await).clone();
        
        if raw_data.is_empty() {
            return Ok(());
        }

        // Calculate aggregated metrics
        let mut total_time_to_first_cert = 0.0;
        let mut total_samples = 0;
        let mut total_replay_tests = 0;
        let mut total_passed_tests = 0;
        let mut total_cert_issuance = 0;
        let mut total_cert_failures = 0;
        let mut all_latency_samples: Vec<f64> = Vec::new();

        for data in &raw_data {
            // Aggregate time-to-first-cert
            for &sample in &data.time_to_first_cert_samples {
                total_time_to_first_cert += sample;
                total_samples += 1;
            }

            // Aggregate replay metrics
            total_replay_tests += data.replay_total_tests;
            total_passed_tests += data.replay_passed_tests;

            // Aggregate certificate metrics
            total_cert_issuance += data.cert_issuance_total;
            total_cert_failures += data.cert_issuance_failures;

            // Collect latency samples for P95 calculation
            all_latency_samples.extend(data.latency_samples.clone());
        }

        // Calculate aggregated metrics
        let avg_time_to_first_cert = if total_samples > 0 {
            total_time_to_first_cert / total_samples as f64
        } else {
            0.0
        };

        let replay_pass_rate = if total_replay_tests > 0 {
            (total_passed_tests as f64 / total_replay_tests as f64) * 100.0
        } else {
            0.0
        };

        let p95_latency = if !all_latency_samples.is_empty() {
            all_latency_samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let index = (all_latency_samples.len() as f64 * 0.95) as usize;
            all_latency_samples[index.min(all_latency_samples.len() - 1)]
        } else {
            0.0
        };

        let cert_success_rate = if total_cert_issuance > 0 {
            ((total_cert_issuance - total_cert_failures) as f64 / total_cert_issuance as f64) * 100.0
        } else {
            0.0
        };

        // Update aggregated metrics
        {
            let mut aggregated = self.aggregated_metrics.write().await;
            *aggregated = AggregatedTelemetry {
                avg_time_to_first_cert,
                replay_pass_rate,
                p95_latency,
                cert_success_rate,
                sample_count: total_samples as u64,
                aggregation_period_hours: self.aggregation_interval_hours,
            };
        }

        info!("Telemetry aggregated: {} samples, avg_time_to_first_cert: {:.3}s, replay_pass_rate: {:.1}%, p95_latency: {:.3}s, cert_success_rate: {:.1}%",
            total_samples, avg_time_to_first_cert, replay_pass_rate, p95_latency, cert_success_rate);

        Ok(())
    }

    async fn start_aggregation_scheduler(&self) {
        let aggregation_interval = Duration::from_secs(self.aggregation_interval_hours * 3600);
        let mut interval = interval(aggregation_interval);
        let service = self.clone();

        tokio::spawn(async move {
            loop {
                interval.tick().await;
                
                if let Err(e) = service.aggregate_telemetry().await {
                    error!("Telemetry aggregation failed: {}", e);
                }
            }
        });

        info!("Telemetry aggregation scheduler started with interval: {:?}", aggregation_interval);
    }

    async fn get_aggregated_metrics(&self) -> AggregatedTelemetry {
        (*self.aggregated_metrics.read().await).clone()
    }

    #[allow(dead_code)] // Public helper for callers hashing tenant IDs before ingest
    fn hash_tenant_id(tenant_id: &str) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(tenant_id.as_bytes());
        format!("{:x}", hasher.finalize())
    }
}

// Implement Clone for TelemetryService
impl Clone for TelemetryService {
    fn clone(&self) -> Self {
        Self {
            aggregated_metrics: self.aggregated_metrics.clone(),
            raw_telemetry: self.raw_telemetry.clone(),
            registry: self.registry.clone(),
            http_client: self.http_client.clone(),
            aggregation_interval_hours: self.aggregation_interval_hours,
            data_retention_hours: self.data_retention_hours,
            opt_in_enabled: self.opt_in_enabled,
        }
    }
}

async fn handle_request(
    req: Request<Body>,
    service: Arc<TelemetryService>,
) -> Result<Response<Body>, hyper::Error> {
    let path = req.uri().path();
    let method = req.method();

    match (method.as_str(), path) {
        ("POST", "/telemetry/collect") => {
            let body_bytes = hyper::body::to_bytes(req.into_body()).await?;
            let telemetry_data: TelemetryData = serde_json::from_slice(&body_bytes)
                .unwrap_or_else(|_| TelemetryData {
                    time_to_first_cert_samples: Vec::new(),
                    replay_total_tests: 0,
                    replay_passed_tests: 0,
                    latency_samples: Vec::new(),
                    cert_issuance_total: 0,
                    cert_issuance_failures: 0,
                    tenant_id_hash: String::new(),
                    timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as i64,
                    version: "1.0".to_string(),
                });

            match service.collect_telemetry(telemetry_data).await {
                Ok(response) => {
                    let response_json = serde_json::to_string(&response).unwrap();
                    
                    Ok(Response::builder()
                        .header("Content-Type", "application/json")
                        .body(Body::from(response_json))
                        .unwrap())
                }
                Err(e) => {
                    let response = TelemetryResponse {
                        success: false,
                        message: format!("Failed to collect telemetry: {}", e),
                        aggregated_data: None,
                    };
                    let response_json = serde_json::to_string(&response).unwrap();
                    
                    Ok(Response::builder()
                        .status(400)
                        .header("Content-Type", "application/json")
                        .body(Body::from(response_json))
                        .unwrap())
                }
            }
        }
        ("GET", "/telemetry/metrics") => {
            let metrics = service.get_aggregated_metrics().await;
            let response_json = serde_json::to_string(&metrics).unwrap();
            
            Ok(Response::builder()
                .header("Content-Type", "application/json")
                .header("Cache-Control", "public, max-age=60") // 1 minute cache
                .body(Body::from(response_json))
                .unwrap())
        }
        ("GET", "/metrics") => {
            let mut buffer = String::new();
            encode(&mut buffer, &service.registry).unwrap();

            Ok(Response::builder()
                .header("Content-Type", "text/plain; version=0.0.4; charset=utf-8")
                .body(Body::from(buffer))
                .unwrap())
        }
        _ => {
            let response = serde_json::json!({
                "error": "Not found",
                "message": "Endpoint not supported"
            });
            
            Ok(Response::builder()
                .status(404)
                .header("Content-Type", "application/json")
                .body(Body::from(response.to_string()))
                .unwrap())
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let service = Arc::new(TelemetryService::new());
    
    // Start aggregation scheduler
    service.start_aggregation_scheduler().await;

    let addr = std::net::SocketAddr::from(([0, 0, 0, 0], 8084));

    let make_svc = make_service_fn(move |_conn| {
        let service = service.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let service = service.clone();
                handle_request(req, service)
            }))
        }
    });

    let server = Server::bind(&addr).serve(make_svc);

    info!("Telemetry Service listening on {}", addr);

    if let Err(e) = server.await {
        error!("Server error: {}", e);
    }

    Ok(())
}
