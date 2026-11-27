// KMS proxy for attestation and key handling; some structs and methods are reserved for future use.
#![allow(dead_code, unused_variables)]

use anyhow::Result;
use base64::Engine;
use chrono::{DateTime, Utc};
use ed25519_dalek::{Signature, VerifyingKey};
use axum::{
    body::{Body, Bytes},
    extract::{DefaultBodyLimit, FromRequest, Request},
    http::Response,
    response::IntoResponse,
    Router,
};
use metrics::{counter, histogram};
use reqwest::Client;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tracing::{error, info, warn};
use uuid::Uuid;

#[derive(Debug, Deserialize, Serialize, Clone)]
#[serde(deny_unknown_fields)]
struct AttestationToken {
    token: String,
    pod_identity: String,
    policy_hash: String,
    timestamp: DateTime<Utc>,
    signature: String,
}

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
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

#[derive(Debug, Deserialize, Serialize)]
struct KmsSignRequest {
    message: String,
    key_id: String,
}

#[derive(Debug, Deserialize, Serialize)]
struct KmsSignResponse {
    signature: String,
    key_id: String,
}

/// Operator-provisioned authority for one explicit signing scope.
/// This verifies an issuer's statement, not hardware attestation itself.
struct AttestationAuthority {
    key: VerifyingKey,
    pod: String,
    policy: String,
    key_id: String,
}

impl AttestationAuthority {
    fn from_environment() -> Option<Self> {
        let key = std::env::var("KMS_ATTESTATION_PUBLIC_KEY").ok()?;
        let raw: [u8; 32] = base64::engine::general_purpose::STANDARD.decode(&key).ok()?.try_into().ok()?;
        let key = VerifyingKey::from_bytes(&raw).ok()?;
        if key.is_weak() { return None; }
        let pod = std::env::var("KMS_ALLOWED_POD_IDENTITY").ok()?;
        let policy = std::env::var("KMS_ALLOWED_POLICY_HASH").ok()?;
        let key_id = std::env::var("KMS_KEY_ID").ok()?;
        if pod.is_empty() || policy.is_empty() || key_id.is_empty() ||
            !key_id.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b'_') {
            return None;
        }
        Some(Self { key, pod, policy, key_id })
    }

    fn authorizes(&self, request: &KmsRequest, now: DateTime<Utc>) -> bool {
        let Some(token) = &request.attestation_token else { return false };
        let Some(data) = &request.data else { return false };
        if token.token.is_empty() || token.pod_identity != self.pod ||
            token.policy_hash != self.policy || request.key_id != self.key_id ||
            request.operation != "sign" || token.timestamp > now ||
            now.signed_duration_since(token.timestamp) > chrono::Duration::seconds(60) ||
            token.timestamp.timestamp_subsec_nanos() >= 1_000_000_000 {
            return false;
        }
        let Ok(bytes) = base64::engine::general_purpose::STANDARD.decode(&token.signature) else { return false };
        let Ok(signature) = Signature::from_slice(&bytes) else { return false };
        self.key.verify_strict(&signing_transcript(token, &request.operation, &request.key_id, data), &signature).is_ok()
    }
}

/// Versioned, length-framed transcript. Bind every input used for authorization
/// and the exact operation, key and data dispatched to the signing provider.
fn signing_transcript(token: &AttestationToken, operation: &str, key_id: &str, data: &str) -> Vec<u8> {
    let mut message = b"PF-KMS-AUTHORIZATION-v1\0".to_vec();
    for value in [&token.token[..], &token.pod_identity, &token.policy_hash, operation, key_id, data] {
        message.extend_from_slice(&(value.len() as u64).to_be_bytes());
        message.extend_from_slice(value.as_bytes());
    }
    message.extend_from_slice(&token.timestamp.timestamp().to_be_bytes());
    message.extend_from_slice(&token.timestamp.timestamp_subsec_nanos().to_be_bytes());
    message
}

struct KmsProxy {
    authority: Option<AttestationAuthority>,
    vault_client: Option<Client>,
    vault_url: String,
    vault_token: String,
    kms_client: Option<Client>,
    kms_endpoint: String,
}

fn trusted_https_client(endpoint: &str) -> Option<Client> {
    let url = reqwest::Url::parse(endpoint).ok()?;
    if url.scheme() != "https" || url.host_str().is_none() ||
        !url.username().is_empty() || url.password().is_some() ||
        url.query().is_some() || url.fragment().is_some() {
        return None;
    }
    Client::builder()
        .timeout(std::time::Duration::from_secs(15))
        .connect_timeout(std::time::Duration::from_secs(5))
        .redirect(reqwest::redirect::Policy::none())
        .build().ok()
}

impl KmsProxy {
    fn new() -> Self {
        let authority = AttestationAuthority::from_environment();
        if authority.is_none() {
            warn!("KMS signing unavailable: operator authorization configuration missing or invalid");
        }
        let vault_url = std::env::var("VAULT_URL").unwrap_or_default();
        let vault_token = std::env::var("VAULT_TOKEN").unwrap_or_default();
        let vault_client = if vault_token.is_empty() { None } else { trusted_https_client(&vault_url) };
        let kms_endpoint = std::env::var("KMS_ENDPOINT").unwrap_or_default();
        let kms_client = trusted_https_client(&kms_endpoint);
        Self { authority, vault_client, vault_url, vault_token, kms_client, kms_endpoint }
    }

    async fn process_kms_request(&self, request: KmsRequest) -> KmsResponse {
        let operation_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();
        let result = if request.operation != "sign" {
            Err(anyhow::anyhow!("Operation unavailable: no qualified implementation"))
        } else if !self.authority.as_ref().map(|a| a.authorizes(&request, timestamp)).unwrap_or(false) {
            Err(anyhow::anyhow!("Attestation authorization rejected"))
        } else if let Some(data) = &request.data {
            self.sign_with_kms(data, &request.key_id).await
        } else {
            Err(anyhow::anyhow!("Missing data"))
        };
        match result {
            Ok(signature) => KmsResponse { success: true, result: Some(signature), error: None, operation_id, timestamp },
            Err(error) => {
                warn!("KMS operation rejected: {}", error);
                KmsResponse { success: false, result: None, error: Some(error.to_string()), operation_id, timestamp }
            }
        }
    }

    /// No fake signature or fallback after a selected provider fails.
    async fn sign_with_kms(&self, data: &str, key_id: &str) -> Result<String> {
        let start = std::time::Instant::now();
        let (result, provider) = if let Some(client) = &self.vault_client {
            (self.sign_with_vault(client, data, key_id).await, "vault")
        } else if let Some(client) = &self.kms_client {
            (self.sign_with_remote_gateway(client, data, key_id).await, "gateway")
        } else {
            return Err(anyhow::anyhow!("No signing provider configured"));
        };
        histogram!("kms_sign_duration_seconds", start.elapsed().as_secs_f64(), "provider" => provider);
        let signature = result?;
        if signature.is_empty() {
            return Err(anyhow::anyhow!("Signing provider returned an empty signature"));
        }
        counter!("kms_sign_success", 1, "provider" => provider);
        Ok(signature)
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
            Ok(vault_response.data.signature)
        } else {
            Err(anyhow::anyhow!(
                "Vault signing failed with status: {}",
                response.status()
            ))
        }
    }

    /// Invoke the configured remote signing gateway (not the AWS KMS API).
    async fn sign_with_remote_gateway(&self, client: &Client, data: &str, key_id: &str) -> Result<String> {
        let url = format!("{}/sign", self.kms_endpoint.trim_end_matches('/'));

        let request_body = KmsSignRequest {
            message: base64::engine::general_purpose::STANDARD.encode(data),
            key_id: key_id.to_string(),
        };

        let response = client
            .post(&url)
            .header("Content-Type", "application/json")
            .json(&request_body)
            .send()
            .await?;

        if response.status().is_success() {
            let kms_response: KmsSignResponse = response.json().await?;
            if kms_response.key_id != key_id {
                return Err(anyhow::anyhow!("Signing gateway returned a different key identity"));
            }
            Ok(kms_response.signature)
        } else {
            Err(anyhow::anyhow!(
                "Signing gateway failed with status: {}",
                response.status()
            ))
        }
    }
}

async fn handle_request(
    req: Request,
    proxy: Arc<KmsProxy>,
) -> Result<Response<Body>, Response<Body>> {
    let path = req.uri().path().to_owned();
    let method = req.method();

    match (method.as_str(), path.as_str()) {
        ("POST", "/kms/encrypt")
        | ("POST", "/kms/decrypt")
        | ("POST", "/kms/sign")
        | ("POST", "/kms/verify") => {
            let body_bytes = Bytes::from_request(req, &()).await
                .map_err(|rejection| rejection.into_response())?;
            let kms_request: KmsRequest = serde_json::from_slice(&body_bytes)
                .map_err(|_| (axum::http::StatusCode::BAD_REQUEST, "Invalid KMS request").into_response())?;
            if path.strip_prefix("/kms/") != Some(kms_request.operation.as_str()) {
                return Err((axum::http::StatusCode::BAD_REQUEST, "Operation does not match route").into_response());
            }

            let response = proxy.process_kms_request(kms_request).await;
            let response_json = serde_json::to_string(&response).unwrap();

            Ok(Response::builder()
                .header("Content-Type", "application/json")
                .body(Body::from(response_json))
                .unwrap())
        }
        ("POST", "/kms/rotate-keys") => {
            Ok((axum::http::StatusCode::NOT_IMPLEMENTED, "Key rotation requires operator provisioning").into_response())
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

// Retain existing method/path dispatch and bound collected request bodies.
const MAX_REQUEST_BODY_BYTES: usize = 2 * 1024 * 1024;

fn http_router(proxy: Arc<KmsProxy>) -> Router {
    Router::new()
        .fallback(move |req: Request| {
            let proxy = proxy.clone();
            async move { handle_request(req, proxy).await }
        })
        .layer(DefaultBodyLimit::max(MAX_REQUEST_BODY_BYTES))
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let proxy = Arc::new(KmsProxy::new());
    let addr = std::net::SocketAddr::from(([127, 0, 0, 1], 8082));

    let listener = tokio::net::TcpListener::bind(addr).await?;
    info!("KMS Proxy listening on {}", addr);
    axum::serve(listener, http_router(proxy)).await?;

    Ok(())
}

#[cfg(test)]
mod http_transport_tests {
    use super::*;

    #[tokio::test]
    async fn test_signed_request_binding_and_provider_dispatch() {
        use ed25519_dalek::{Signer, SigningKey};
        use std::sync::atomic::{AtomicUsize, Ordering};

        let issuer = SigningKey::from_bytes(&[19; 32]);
        let authority = AttestationAuthority {
            key: issuer.verifying_key(), pod: "fixture-pod".into(),
            policy: "fixture-policy".into(), key_id: "fixture-key".into(),
        };
        let calls = Arc::new(AtomicUsize::new(0));
        let observed = calls.clone();
        let provider = Router::new().route("/sign", axum::routing::post(move |axum::Json(request): axum::Json<KmsSignRequest>| {
            let observed = observed.clone();
            async move {
                assert_eq!(request.key_id, "fixture-key");
                assert_eq!(base64::engine::general_purpose::STANDARD.decode(request.message).unwrap(), b"fixture-data");
                observed.fetch_add(1, Ordering::SeqCst);
                axum::Json(KmsSignResponse { signature: "fixture-provider-response".into(), key_id: request.key_id })
            }
        }));
        let provider_listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let provider_addr = provider_listener.local_addr().unwrap();
        let upstream = tokio::spawn(async move { axum::serve(provider_listener, provider).await.unwrap() });
        let client = Client::builder().no_proxy().timeout(std::time::Duration::from_secs(5)).build().unwrap();
        let proxy = KmsProxy {
            authority: Some(authority), vault_client: None, vault_url: String::new(), vault_token: String::new(),
            kms_client: Some(client.clone()), kms_endpoint: format!("http://{provider_addr}"),
        };
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let server = tokio::spawn(async move { axum::serve(listener, http_router(Arc::new(proxy))).await.unwrap() });
        let mut request = KmsRequest {
            operation: "sign".into(), key_id: "fixture-key".into(), data: Some("fixture-data".into()),
            attestation_token: Some(AttestationToken {
                token: "fixture-nonce".into(), pod_identity: "fixture-pod".into(),
                policy_hash: "fixture-policy".into(), timestamp: Utc::now(), signature: String::new(),
            }),
        };
        let token = request.attestation_token.as_mut().unwrap();
        token.signature = base64::engine::general_purpose::STANDARD.encode(
            issuer.sign(&signing_transcript(token, "sign", "fixture-key", "fixture-data")).to_bytes());
        let valid = serde_json::to_value(&request).unwrap();
        let url = format!("http://{addr}/kms/sign");
        let response: serde_json::Value = client.post(&url).json(&valid).send().await.unwrap().json().await.unwrap();
        assert_eq!(response["success"], true);
        assert_eq!(calls.load(Ordering::SeqCst), 1);

        for (field, value) in [
            ("signature", serde_json::json!("sig_forged")),
            ("pod_identity", serde_json::json!("other")),
            ("policy_hash", serde_json::json!("other")),
            ("token", serde_json::json!("different-nonce")),
            ("timestamp", serde_json::json!((Utc::now() + chrono::Duration::seconds(10)).to_rfc3339())),
            ("timestamp", serde_json::json!((Utc::now() - chrono::Duration::seconds(61)).to_rfc3339())),
        ] {
            let mut changed = valid.clone();
            changed["attestation_token"][field] = value;
            let response: serde_json::Value = client.post(&url).json(&changed).send().await.unwrap().json().await.unwrap();
            assert_eq!(response["success"], false, "mutation: {field}");
        }
        for (field, value) in [
            ("attestation_token", serde_json::Value::Null),
            ("data", serde_json::json!("other-data")),
            ("key_id", serde_json::json!("other-key")),
        ] {
            let mut changed = valid.clone();
            changed[field] = value;
            let response: serde_json::Value = client.post(&url).json(&changed).send().await.unwrap().json().await.unwrap();
            assert_eq!(response["success"], false, "mutation: {field}");
        }
        let response = client.post(format!("http://{addr}/kms/encrypt")).json(&valid).send().await.unwrap();
        assert_eq!(response.status().as_u16(), 400);
        let response = client.post(format!("http://{addr}/kms/rotate-keys")).send().await.unwrap();
        assert_eq!(response.status().as_u16(), 501);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        server.abort();
        upstream.abort();
    }

    #[tokio::test]
    async fn test_loopback_dispatch_and_body_limit() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let app = http_router(Arc::new(KmsProxy::new()));
        let server = tokio::spawn(async move {
            axum::serve(listener, app).await.unwrap();
        });
        let client = Client::builder().no_proxy()
            .timeout(std::time::Duration::from_secs(5)).build().unwrap();
        let base = format!("http://{addr}");
        let unknown = client.get(format!("{base}/unknown")).send().await.unwrap();
        assert_eq!(unknown.status().as_u16(), 404);
        assert_eq!(unknown.json::<serde_json::Value>().await.unwrap()["error"], "Not found");
        
        let oversized = client.post(format!("{base}/kms/encrypt"))
            .body(vec![b'x'; MAX_REQUEST_BODY_BYTES + 1]).send().await.unwrap();
        assert_eq!(oversized.status().as_u16(), 413);
        server.abort();
    }
}
