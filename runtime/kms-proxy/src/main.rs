use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tracing::{error, info, warn};
use uuid::Uuid;
use redis::AsyncCommands;
use metrics::{counter, histogram, gauge};

#[derive(Debug, Deserialize, Serialize)]
struct AttestationToken {
    token: String,
    pod_identity: String,
    policy_hash: String,
    timestamp: DateTime<Utc>,
    signature: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct KmsRequest {
    operation: String, // "encrypt", "decrypt", "sign", "verify"
    key_id: String,
    data: Option<String>,
    attestation_token: Option<AttestationToken>,
}

#[derive(Debug, Serialize)]
struct KmsResponse {
    success: bool,
    result: Option<String>,
    error: Option<String>,
    operation_id: String,
    timestamp: DateTime<Utc>,
}

#[derive(Debug, Serialize)]
struct AttestationValidation {
    valid: bool,
    reason: String,
    policy_hash_match: bool,
    pod_identity_valid: bool,
    token_fresh: bool,
}

struct KmsProxy {
    attestation_cache: Arc<RwLock<HashMap<String, AttestationToken>>>,
    kek_cache: Arc<RwLock<HashMap<String, String>>>, // KEK handle cache
    redis_client: Option<redis::Client>,
    cache_ttl_seconds: u64,
    allowed_policy_hashes: Vec<String>,
    allowed_pod_identities: Vec<String>,
}

impl KmsProxy {
    fn new() -> Self {
        // Initialize Redis client if available
        let redis_client = std::env::var("REDIS_URL")
            .ok()
            .and_then(|url| redis::Client::open(url).ok());

        if redis_client.is_some() {
            info!("Redis caching enabled for KMS proxy");
        } else {
            warn!("Redis not available, using in-memory cache only");
        }

        Self {
            attestation_cache: Arc::new(RwLock::new(HashMap::new())),
            kek_cache: Arc::new(RwLock::new(HashMap::new())),
            redis_client,
            cache_ttl_seconds: 60, // 60 second cache validity
            allowed_policy_hashes: vec![
                "default_policy_hash".to_string(),
                "secure_policy_hash".to_string(),
            ],
            allowed_pod_identities: vec![
                "pod-secure-1".to_string(),
                "pod-secure-2".to_string(),
            ],
        }
    }

    async fn validate_attestation(&self, token: &AttestationToken) -> AttestationValidation {
        let start_time = std::time::Instant::now();
        let now = Utc::now();
        let token_age = now.signed_duration_since(token.timestamp).num_seconds() as u64;

        // Check Redis cache first
        if let Some(ref redis_client) = self.redis_client {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                let cache_key = format!("attestation:{}:{}", token.policy_hash, token.pod_identity);
                if let Ok(cached_result) = conn.get::<_, Option<String>>(&cache_key).await {
                    if let Some(cached) = cached_result {
                        if let Ok(validation) = serde_json::from_str::<AttestationValidation>(&cached) {
                            counter!("kms_cache_hit", 1);
                            let latency = start_time.elapsed();
                            histogram!("attestation_validation_duration_seconds", latency.as_secs_f64());
                            return validation;
                        }
                    }
                }
            }
        }

        // Check in-memory cache
        let cache_key = format!("{}:{}", token.policy_hash, token.pod_identity);
        let attestation_cache = self.attestation_cache.read().await;
        if let Some(cached_token) = attestation_cache.get(&cache_key) {
            let token_age_cached = now.signed_duration_since(cached_token.timestamp).num_seconds() as u64;
            if token_age_cached <= self.cache_ttl_seconds {
                counter!("kms_cache_hit", 1);
                let latency = start_time.elapsed();
                histogram!("attestation_validation_duration_seconds", latency.as_secs_f64());
                return AttestationValidation {
                    valid: true,
                    reason: "Valid cached attestation".to_string(),
                    policy_hash_match: true,
                    pod_identity_valid: true,
                    token_fresh: true,
                };
            }
        }
        drop(attestation_cache);

        // Perform validation
        let token_fresh = token_age <= self.cache_ttl_seconds;
        let policy_hash_match = self.allowed_policy_hashes.contains(&token.policy_hash);
        let pod_identity_valid = self.allowed_pod_identities.contains(&token.pod_identity);
        let signature_valid = self.verify_signature(token);

        let valid = token_fresh && policy_hash_match && pod_identity_valid && signature_valid;

        let reason = if !token_fresh {
            "Token expired (older than 60 seconds)".to_string()
        } else if !policy_hash_match {
            "Policy hash not in allowed list".to_string()
        } else if !pod_identity_valid {
            "Pod identity not in allowed list".to_string()
        } else if !signature_valid {
            "Invalid signature".to_string()
        } else {
            "Valid attestation".to_string()
        };

        let validation = AttestationValidation {
            valid,
            reason: reason.clone(),
            policy_hash_match,
            pod_identity_valid,
            token_fresh,
        };

        // Cache the result
        if valid {
            let cache_key = format!("{}:{}", token.policy_hash, token.pod_identity);
            let mut attestation_cache = self.attestation_cache.write().await;
            attestation_cache.insert(cache_key.clone(), token.clone());

            // Also cache in Redis if available
            if let Some(ref redis_client) = self.redis_client {
                if let Ok(mut conn) = redis_client.get_async_connection().await {
                    let redis_key = format!("attestation:{}:{}", token.policy_hash, token.pod_identity);
                    let _: Result<(), redis::RedisError> = conn.set_ex(
                        &redis_key,
                        serde_json::to_string(&validation).unwrap(),
                        self.cache_ttl_seconds as usize,
                    ).await;
                }
            }
        }

        counter!("kms_cache_miss", 1);
        let latency = start_time.elapsed();
        histogram!("attestation_validation_duration_seconds", latency.as_secs_f64());

        validation
    }

    fn verify_signature(&self, token: &AttestationToken) -> bool {
        // In production, would verify cryptographic signature
        // For now, just check that signature exists and has expected format
        !token.signature.is_empty() && token.signature.starts_with("sig_")
    }

    async fn process_kms_request(&self, request: KmsRequest) -> KmsResponse {
        let operation_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();

        // Check if attestation token is required and provided
        if let Some(token) = &request.attestation_token {
            let validation = self.validate_attestation(token).await;

            if !validation.valid {
                error!("Attestation validation failed: {}", validation.reason);
                return KmsResponse {
                    success: false,
                    result: None,
                    error: Some(format!("Attestation failed: {}", validation.reason)),
                    operation_id,
                    timestamp,
                };
            }

            // Cache the valid attestation
            let mut cache = self.attestation_cache.write().await;
            cache.insert(token.pod_identity.clone(), token.clone());
            info!("Attestation validated and cached for pod: {}", token.pod_identity);
        } else {
            // Check if we have a cached attestation for this operation
            // In a real implementation, we'd extract pod identity from request context
            let cache = self.attestation_cache.read().await;
            if cache.is_empty() {
                error!("No attestation token provided and no cached attestation");
                return KmsResponse {
                    success: false,
                    result: None,
                    error: Some("Attestation token required".to_string()),
                    operation_id,
                    timestamp,
                };
            }
        }

        // Simulate KMS operation
        let result = match request.operation.as_str() {
            "encrypt" => {
                if let Some(data) = request.data {
                    Some(format!("encrypted_{}", data))
                } else {
                    None
                }
            }
            "decrypt" => {
                if let Some(data) = request.data {
                    Some(data.replace("encrypted_", ""))
                } else {
                    None
                }
            }
            "sign" => {
                if let Some(data) = request.data {
                    Some(format!("signed_{}", data))
                } else {
                    None
                }
            }
            "verify" => {
                if let Some(data) = request.data {
                    Some("signature_valid".to_string())
                } else {
                    None
                }
            }
            _ => None,
        };

        if result.is_some() {
            info!("KMS operation '{}' completed successfully", request.operation);
            KmsResponse {
                success: true,
                result,
                error: None,
                operation_id,
                timestamp,
            }
        } else {
            error!("KMS operation '{}' failed", request.operation);
            KmsResponse {
                success: false,
                result: None,
                error: Some("Invalid operation or missing data".to_string()),
                operation_id,
                timestamp,
            }
        }
    }

    async fn rotate_attestation_keys(&self) {
        // In production, this would rotate the keys used for attestation verification
        info!("Rotating attestation keys");
        
        // Clear the cache to force fresh attestations
        let mut cache = self.attestation_cache.write().await;
        cache.clear();
        info!("Attestation cache cleared");
    }

    async fn get_kek_handle(&self, policy_hash: &str) -> Result<String> {
        let start_time = std::time::Instant::now();

        // Check in-memory cache first
        let kek_cache = self.kek_cache.read().await;
        if let Some(handle) = kek_cache.get(policy_hash) {
            counter!("kms_cache_hit", 1);
            let latency = start_time.elapsed();
            histogram!("kek_retrieval_duration_seconds", latency.as_secs_f64());
            return Ok(handle.clone());
        }
        drop(kek_cache);

        // Check Redis cache
        if let Some(ref redis_client) = self.redis_client {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                let cache_key = format!("kek:{}", policy_hash);
                if let Ok(cached_handle) = conn.get::<_, Option<String>>(&cache_key).await {
                    if let Some(handle) = cached_handle {
                        // Update in-memory cache
                        let mut kek_cache = self.kek_cache.write().await;
                        kek_cache.insert(policy_hash.to_string(), handle.clone());
                        
                        counter!("kms_cache_hit", 1);
                        let latency = start_time.elapsed();
                        histogram!("kek_retrieval_duration_seconds", latency.as_secs_f64());
                        return Ok(handle);
                    }
                }
            }
        }

        // Fetch from KMS (simulated)
        let kek_handle = format!("kek-{}", Uuid::new_v4());
        
        // Cache the result
        let mut kek_cache = self.kek_cache.write().await;
        kek_cache.insert(policy_hash.to_string(), kek_handle.clone());

        // Also cache in Redis if available
        if let Some(ref redis_client) = self.redis_client {
            if let Ok(mut conn) = redis_client.get_async_connection().await {
                let cache_key = format!("kek:{}", policy_hash);
                let _: Result<(), redis::RedisError> = conn.set_ex(
                    &cache_key,
                    &kek_handle,
                    self.cache_ttl_seconds as usize,
                ).await;
            }
        }

        counter!("kms_cache_miss", 1);
        let latency = start_time.elapsed();
        histogram!("kek_retrieval_duration_seconds", latency.as_secs_f64());

        Ok(kek_handle)
    }
}

async fn handle_request(
    req: Request<Body>,
    proxy: Arc<KmsProxy>,
) -> Result<Response<Body>, hyper::Error> {
    let path = req.uri().path();
    let method = req.method();

    match (method.as_str(), path) {
        ("POST", "/kms/encrypt") | ("POST", "/kms/decrypt") | ("POST", "/kms/sign") | ("POST", "/kms/verify") => {
            let body_bytes = hyper::body::to_bytes(req.into_body()).await?;
            let kms_request: KmsRequest = serde_json::from_slice(&body_bytes)
                .unwrap_or_else(|_| KmsRequest {
                    operation: "unknown".to_string(),
                    key_id: "".to_string(),
                    data: None,
                    attestation_token: None,
                });

            let response = proxy.process_kms_request(kms_request).await;
            let response_json = serde_json::to_string(&response).unwrap();
            
            Ok(Response::builder()
                .header("Content-Type", "application/json")
                .body(Body::from(response_json))
                .unwrap())
        }
        ("POST", "/kms/rotate-keys") => {
            proxy.rotate_attestation_keys().await;
            let response = serde_json::json!({
                "success": true,
                "message": "Attestation keys rotated"
            });
            
            Ok(Response::builder()
                .header("Content-Type", "application/json")
                .body(Body::from(response.to_string()))
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

    let proxy = Arc::new(KmsProxy::new());
    let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 8082));

    let make_svc = make_service_fn(move |_conn| {
        let proxy = proxy.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let proxy = proxy.clone();
                handle_request(req, proxy)
            }))
        }
    });

    let server = Server::bind(&addr).serve(make_svc);

    info!("KMS Proxy listening on {}", addr);

    if let Err(e) = server.await {
        error!("Server error: {}", e);
    }

    Ok(())
} 