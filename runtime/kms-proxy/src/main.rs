// KMS proxy for attestation and key handling; some structs and methods are reserved for future use.
#![allow(dead_code, unused_variables)]

use anyhow::Result;
use base64::Engine;
use chrono::{DateTime, Utc};
use hyper::{
    body::HttpBody,
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server, StatusCode,
};
use metrics::{counter, histogram};
use redis::AsyncCommands;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn};
use uuid::Uuid;

mod authority;
use authority::RequestAuthority;

#[derive(Debug, Deserialize, Serialize, Clone)]
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

#[derive(Debug, Serialize, Deserialize)]
struct AttestationValidation {
    valid: bool,
    reason: String,
    policy_hash_match: bool,
    pod_identity_valid: bool,
    token_fresh: bool,
}

#[derive(Debug, Deserialize, Serialize)]
struct VaultAuthResponse {
    auth: VaultAuth,
}

#[derive(Debug, Deserialize, Serialize)]
struct VaultAuth {
    client_token: String,
    lease_duration: u64,
    renewable: bool,
}

#[derive(Debug, Deserialize, Serialize)]
struct VaultSignRequest {
    input: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct VaultSignResponse {
    data: VaultSignData,
}

#[derive(Debug, Deserialize, Serialize)]
struct VaultSignData {
    signature: String,
}

struct KmsProxy {
    authority: Option<RequestAuthority>,
    kek_cache: Arc<RwLock<HashMap<String, String>>>, // KEK handle cache
    redis_client: Option<redis::Client>,
    cache_ttl_seconds: u64,
    vault_client: Option<Client>,
    vault_url: String,
    vault_token: String,
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

        // Only an independently provisioned issuer grants request authority.
        let authority = match RequestAuthority::from_env() {
            Ok(value) => Some(value),
            Err(_) => {
                warn!("KMS request authority unavailable; all signing requests will be denied");
                None
            }
        };

        let vault_url = std::env::var("VAULT_URL").unwrap_or_default();
        let vault_token = std::env::var("VAULT_TOKEN").unwrap_or_default();
        let vault_client = if !vault_token.is_empty() && valid_vault_endpoint(&vault_url) {
            match Client::builder()
                .redirect(reqwest::redirect::Policy::none())
                .timeout(std::time::Duration::from_secs(10))
                .build()
            {
                Ok(client) => Some(client),
                Err(_) => {
                    warn!("Vault HTTP client initialization failed");
                    None
                }
            }
        } else {
            warn!("Vault transit signing unavailable");
            None
        };

        Self {
            authority,
            kek_cache: Arc::new(RwLock::new(HashMap::new())),
            redis_client,
            cache_ttl_seconds: 60, // 60 second cache validity
            vault_client,
            vault_url,
            vault_token,
        }
    }

    fn validate_attestation(&self, request: &KmsRequest) -> AttestationValidation {
        match &self.authority {
            Some(authority) => authority.validate(request),
            None => authority::denied("Trusted request authority unavailable"),
        }
    }

    async fn process_kms_request(&self, request: KmsRequest) -> (StatusCode, KmsResponse) {
        let operation_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();
        let failure = |status, message: &str| (status, KmsResponse {
            success: false,
            result: None,
            error: Some(message.to_owned()),
            operation_id: operation_id.clone(),
            timestamp,
        });

        if request.operation != "sign" {
            return failure(StatusCode::NOT_IMPLEMENTED, "Operation not implemented");
        }
        if !valid_key_id(&request.key_id) {
            return failure(StatusCode::BAD_REQUEST, "Invalid key identifier");
        }
        let Some(data) = &request.data else {
            return failure(StatusCode::BAD_REQUEST, "Signing data required");
        };
        let validation = self.validate_attestation(&request);
        if !validation.valid {
            return failure(StatusCode::FORBIDDEN, &validation.reason);
        }

        match self.sign_with_kms(data, &request.key_id).await {
            Ok(signature) => (StatusCode::OK, KmsResponse {
                success: true,
                result: Some(signature),
                error: None,
                operation_id,
                timestamp,
            }),
            Err(_) => failure(StatusCode::BAD_GATEWAY, "Trusted signing provider unavailable or failed"),
        }
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
            if let Ok(mut conn) = redis_client.get_multiplexed_async_connection().await {
                let cache_key = format!("kek:{}", policy_hash);
                if let Ok(Some(handle)) = conn.get::<_, Option<String>>(&cache_key).await {
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

        // Fetch from KMS (simulated)
        let kek_handle = format!("kek-{}", Uuid::new_v4());

        // Cache the result
        let mut kek_cache = self.kek_cache.write().await;
        kek_cache.insert(policy_hash.to_string(), kek_handle.clone());

        // Also cache in Redis if available
        if let Some(ref redis_client) = self.redis_client {
            if let Ok(mut conn) = redis_client.get_multiplexed_async_connection().await {
                let cache_key = format!("kek:{}", policy_hash);
                let _: Result<(), redis::RedisError> = conn
                    .set_ex(&cache_key, &kek_handle, self.cache_ttl_seconds)
                    .await;
            }
        }

        counter!("kms_cache_miss", 1);
        let latency = start_time.elapsed();
        histogram!("kek_retrieval_duration_seconds", latency.as_secs_f64());

        Ok(kek_handle)
    }

    /// Sign through the explicitly configured Vault transit service.
    /// Provider absence or failure is an error, never a mock success.
    async fn sign_with_kms(&self, data: &str, key_id: &str) -> Result<String> {
        let client = self.vault_client.as_ref()
            .ok_or_else(|| anyhow::anyhow!("Vault transit signing unavailable"))?;
        let start_time = std::time::Instant::now();
        let result = self.sign_with_vault(client, data, key_id).await;
        histogram!("kms_sign_duration_seconds", start_time.elapsed().as_secs_f64(), "provider" => "vault");
        if result.is_ok() {
            counter!("kms_sign_success", 1, "provider" => "vault");
        } else {
            counter!("kms_sign_failure", 1, "provider" => "vault");
        }
        result
    }

    /// Sign data using HashiCorp Vault
    async fn sign_with_vault(&self, client: &Client, data: &str, key_id: &str) -> Result<String> {
        let url = format!("{}/v1/transit/sign/{}", self.vault_url.trim_end_matches('/'), key_id);

        let request_body = VaultSignRequest {
            input: base64::engine::general_purpose::STANDARD.encode(data),
        };

        let response = client
            .post(&url)
            .header("X-Vault-Token", &self.vault_token)
            .header("Content-Type", "application/json")
            .json(&request_body)
            .send()
            .await?;

        if response.status().is_success() {
            let vault_response: VaultSignResponse = response.json().await?;
            let signature = vault_response.data.signature;
            if !valid_vault_signature_format(&signature) {
                return Err(anyhow::anyhow!("Vault returned an invalid signature representation"));
            }
            Ok(signature)
        } else {
            Err(anyhow::anyhow!(
                "Vault signing failed with status: {}",
                response.status()
            ))
        }
    }

}

// Restrict identifiers interpolated into the transit URL to a single safe segment.
fn valid_key_id(value: &str) -> bool {
    !value.is_empty() && value.len() <= 128
        && value.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

fn valid_vault_endpoint(value: &str) -> bool {
    let Ok(url) = reqwest::Url::parse(value) else { return false; };
    let transport_ok = url.scheme() == "https" || (
        url.scheme() == "http" && matches!(url.host_str(), Some("127.0.0.1" | "[::1]" | "::1"))
    );
    transport_ok && url.host_str().is_some() && url.username().is_empty()
        && url.password().is_none() && url.query().is_none()
        && url.fragment().is_none() && url.path() == "/"
}

// This is a wire-format check, not independent cryptographic verification.
fn valid_vault_signature_format(value: &str) -> bool {
    let Some(rest) = value.strip_prefix("vault:v") else { return false; };
    let Some((version, signature)) = rest.split_once(':') else { return false; };
    matches!(version.parse::<u64>(), Ok(v) if v > 0)
        && matches!(base64::engine::general_purpose::STANDARD.decode(signature), Ok(bytes) if !bytes.is_empty())
}

const MAX_REQUEST_BODY_BYTES: usize = 2 * 1024 * 1024;

async fn read_bounded_body(mut body: Body) -> std::result::Result<Vec<u8>, StatusCode> {
    let mut collected = Vec::new();
    while let Some(chunk) = body.data().await {
        let chunk = chunk.map_err(|_| StatusCode::BAD_REQUEST)?;
        if chunk.len() > MAX_REQUEST_BODY_BYTES - collected.len() {
            return Err(StatusCode::PAYLOAD_TOO_LARGE);
        }
        collected.extend_from_slice(&chunk);
    }
    Ok(collected)
}

fn json_response(status: StatusCode, value: serde_json::Value) -> Response<Body> {
    Response::builder()
        .status(status)
        .header("Content-Type", "application/json")
        .body(Body::from(value.to_string()))
        .expect("constant HTTP response headers")
}

fn error_response(status: StatusCode, message: &str) -> Response<Body> {
    json_response(status, serde_json::json!({"success": false, "error": message}))
}

async fn handle_request(
    req: Request<Body>,
    proxy: Arc<KmsProxy>,
) -> Result<Response<Body>, hyper::Error> {
    if req.method() != hyper::Method::POST {
        return Ok(error_response(StatusCode::NOT_FOUND, "Endpoint not supported"));
    }
    match req.uri().path() {
        "/kms/encrypt" | "/kms/decrypt" | "/kms/verify" | "/kms/rotate-keys" => {
            return Ok(error_response(StatusCode::NOT_IMPLEMENTED, "Operation not implemented"));
        }
        "/kms/sign" => {}
        _ => return Ok(error_response(StatusCode::NOT_FOUND, "Endpoint not supported")),
    }
    let bytes = match read_bounded_body(req.into_body()).await {
        Ok(bytes) => bytes,
        Err(status) => return Ok(error_response(status, "Invalid or oversized request body")),
    };
    let request: KmsRequest = match serde_json::from_slice(&bytes) {
        Ok(request) => request,
        Err(_) => return Ok(error_response(StatusCode::BAD_REQUEST, "Invalid request JSON")),
    };
    if request.operation != "sign" {
        return Ok(error_response(StatusCode::BAD_REQUEST, "Operation does not match endpoint"));
    }
    let (status, response) = proxy.process_kms_request(request).await;
    match serde_json::to_value(response) {
        Ok(value) => Ok(json_response(status, value)),
        Err(_) => Ok(error_response(StatusCode::INTERNAL_SERVER_ERROR, "Response encoding failed")),
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

    server.await?;
    Ok(())
}
