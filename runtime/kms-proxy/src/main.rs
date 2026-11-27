// KMS signing proxy with independently verified request authorization.

use anyhow::Result;
use base64::Engine;
use crate::utc_timestamp::UtcTimestamp;
use axum::{
    body::Body,
    extract::{Request, State},
    http::{Method, Response, StatusCode},
    Router,
};
use futures::StreamExt;
use metrics::{counter, histogram};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tracing::{info, warn};
use uuid::Uuid;

mod authority;
mod utc_timestamp;
use authority::RequestAuthority;

#[cfg(test)]
mod request_tests;

#[derive(Debug, Deserialize, Serialize, Clone)]
struct AttestationToken {
    token: String,
    pod_identity: String,
    policy_hash: String,
    timestamp: UtcTimestamp,
    signature: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct KmsRequest {
    operation: String, // only sign is implemented
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
    timestamp: UtcTimestamp,
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
    vault_client: Option<Client>,
    vault_url: String,
    vault_token: String,
}

impl KmsProxy {
    fn new() -> Self {
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
                .no_proxy()
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
        let timestamp = UtcTimestamp::now();
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
        let url = reqwest::Url::parse(&self.vault_url)?.join(&format!("v1/transit/sign/{key_id}"))?;

        let request_body = VaultSignRequest {
            input: base64::engine::general_purpose::STANDARD.encode(data),
        };

        let mut response = client
            .post(url)
            .header("X-Vault-Token", &self.vault_token)
            .header("Content-Type", "application/json")
            .json(&request_body)
            .send()
            .await?;

        if response.status().is_success() {
            // Bound the provider response independently of request size.
            const MAX_PROVIDER_RESPONSE_BYTES: usize = 64 * 1024;
            let mut bytes = Vec::new();
            while let Some(chunk) = response.chunk().await? {
                if chunk.len() > MAX_PROVIDER_RESPONSE_BYTES - bytes.len() {
                    return Err(anyhow::anyhow!("Vault response exceeds supported size"));
                }
                bytes.extend_from_slice(&chunk);
            }
            let vault_response: VaultSignResponse = serde_json::from_slice(&bytes)?;
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
    if value.trim() != value || value.contains('\\') { return false; }
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

async fn read_bounded_body(body: Body) -> std::result::Result<Vec<u8>, StatusCode> {
    let mut collected = Vec::new();
    let mut stream = body.into_data_stream();
    while let Some(chunk) = stream.next().await {
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
    req: Request,
    proxy: Arc<KmsProxy>,
) -> Response<Body> {
    if req.method() != Method::POST {
        return error_response(StatusCode::NOT_FOUND, "Endpoint not supported");
    }
    match req.uri().path() {
        "/kms/encrypt" | "/kms/decrypt" | "/kms/verify" | "/kms/rotate-keys" => {
            return error_response(StatusCode::NOT_IMPLEMENTED, "Operation not implemented");
        }
        "/kms/sign" => {}
        _ => return error_response(StatusCode::NOT_FOUND, "Endpoint not supported"),
    }
    let bytes = match read_bounded_body(req.into_body()).await {
        Ok(bytes) => bytes,
        Err(status) => return error_response(status, "Invalid or oversized request body"),
    };
    let request: KmsRequest = match serde_json::from_slice(&bytes) {
        Ok(request) => request,
        Err(_) => return error_response(StatusCode::BAD_REQUEST, "Invalid request JSON"),
    };
    if request.operation != "sign" {
        return error_response(StatusCode::BAD_REQUEST, "Operation does not match endpoint");
    }
    let (status, response) = proxy.process_kms_request(request).await;
    match serde_json::to_value(response) {
        Ok(value) => json_response(status, value),
        Err(_) => error_response(StatusCode::INTERNAL_SERVER_ERROR, "Response encoding failed"),
    }
}

fn app(proxy: Arc<KmsProxy>) -> Router {
    Router::new().fallback(|State(proxy): State<Arc<KmsProxy>>, req: Request| async move {
        handle_request(req, proxy).await
    }).with_state(proxy)
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 8082));
    let listener = tokio::net::TcpListener::bind(addr).await?;
    info!("KMS Proxy listening on {}", listener.local_addr()?);
    axum::serve(listener, app(Arc::new(KmsProxy::new()))).await?;
    Ok(())
}
