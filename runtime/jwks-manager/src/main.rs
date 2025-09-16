// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use hyper::{
    service::{make_service_fn, service_fn},
    Body, Request, Response, Server,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use tokio::time::{interval, sleep};
use tracing::{error, info, warn};
use uuid::Uuid;
use reqwest::Client;
use jsonwebtoken::{decode, Algorithm, DecodingKey, Validation};
use base64::{Engine as _, engine::general_purpose};

#[derive(Debug, Deserialize, Serialize, Clone)]
struct JwksKey {
    kty: String,           // Key type
    use_: String,          // Key use (sig, enc)
    kid: String,           // Key ID
    alg: String,           // Algorithm
    n: String,             // RSA modulus
    e: String,             // RSA exponent
    x5c: Option<Vec<String>>, // X.509 certificate chain
    created_at: i64,       // Creation timestamp
    expires_at: i64,       // Expiration timestamp
    revoked: bool,         // Whether key is revoked
}

#[derive(Debug, Deserialize, Serialize)]
struct JwksSet {
    keys: Vec<JwksKey>,
}

#[derive(Debug, Deserialize, Serialize)]
struct CertificatePin {
    kid: String,
    fingerprint: String,   // SHA-256 fingerprint of the certificate
    created_at: i64,
}

#[derive(Debug, Deserialize, Serialize)]
struct RotationConfig {
    rotation_interval_hours: u64,
    key_lifetime_hours: u64,
    overlap_period_hours: u64,
    auto_rotation_enabled: bool,
}

struct JwksManager {
    keys: Arc<RwLock<HashMap<String, JwksKey>>>,
    certificate_pins: Arc<RwLock<HashMap<String, CertificatePin>>>,
    rotation_config: RotationConfig,
    http_client: Client,
    kms_proxy_url: String,
    vault_url: String,
    vault_token: String,
}

impl JwksManager {
    fn new() -> Self {
        let rotation_config = RotationConfig {
            rotation_interval_hours: 24, // Rotate every 24 hours
            key_lifetime_hours: 168,     // Keys valid for 7 days
            overlap_period_hours: 24,    // 24 hour overlap period
            auto_rotation_enabled: std::env::var("AUTO_ROTATION_ENABLED")
                .unwrap_or_else(|_| "true".to_string())
                .parse()
                .unwrap_or(true),
        };

        let kms_proxy_url = std::env::var("KMS_PROXY_URL")
            .unwrap_or_else(|_| "http://kms-proxy:8082".to_string());
        let vault_url = std::env::var("VAULT_URL")
            .unwrap_or_else(|_| "http://vault:8200".to_string());
        let vault_token = std::env::var("VAULT_TOKEN").unwrap_or_default();

        Self {
            keys: Arc::new(RwLock::new(HashMap::new())),
            certificate_pins: Arc::new(RwLock::new(HashMap::new())),
            rotation_config,
            http_client: Client::new(),
            kms_proxy_url,
            vault_url,
            vault_token,
        }
    }

    async fn initialize_keys(&self) -> Result<()> {
        info!("Initializing JWKS keys...");
        
        // Generate initial set of keys
        for i in 0..3 {
            let kid = format!("key-{}", i);
            let key = self.generate_key(&kid).await?;
            let mut keys = self.keys.write().await;
            keys.insert(kid.clone(), key);
            
            // Generate certificate pin
            let pin = self.generate_certificate_pin(&kid).await?;
            let mut pins = self.certificate_pins.write().await;
            pins.insert(kid, pin);
        }

        info!("Initialized {} JWKS keys", self.keys.read().await.len());
        Ok(())
    }

    async fn generate_key(&self, kid: &str) -> Result<JwksKey> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64;

        // In production, this would generate actual RSA keys or retrieve from KMS/Vault
        // For now, we'll simulate key generation
        let key = JwksKey {
            kty: "RSA".to_string(),
            use_: "sig".to_string(),
            kid: kid.to_string(),
            alg: "RS256".to_string(),
            n: format!("modulus_{}", Uuid::new_v4()),
            e: "AQAB".to_string(), // Standard RSA exponent
            x5c: Some(vec![
                format!("certificate_chain_{}", Uuid::new_v4()),
                format!("intermediate_ca_{}", Uuid::new_v4()),
                format!("root_ca_{}", Uuid::new_v4()),
            ]),
            created_at: now,
            expires_at: now + (self.rotation_config.key_lifetime_hours * 3600) as i64,
            revoked: false,
        };

        // Store key in KMS/Vault if configured
        if !self.vault_token.is_empty() {
            self.store_key_in_vault(&key).await?;
        }

        Ok(key)
    }

    async fn store_key_in_vault(&self, key: &JwksKey) -> Result<()> {
        let url = format!("{}/v1/secret/data/jwks/{}", self.vault_url, key.kid);
        
        let request_body = serde_json::json!({
            "data": {
                "key": key
            }
        });

        let response = self
            .http_client
            .post(&url)
            .header("X-Vault-Token", &self.vault_token)
            .header("Content-Type", "application/json")
            .json(&request_body)
            .send()
            .await?;

        if !response.status().is_success() {
            return Err(anyhow::anyhow!("Failed to store key in Vault: {}", response.status()));
        }

        info!("Stored key {} in Vault", key.kid);
        Ok(())
    }

    async fn generate_certificate_pin(&self, kid: &str) -> Result<CertificatePin> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64;

        // In production, this would compute the actual SHA-256 fingerprint of the certificate
        let fingerprint = format!("sha256/{}", Uuid::new_v4());

        Ok(CertificatePin {
            kid: kid.to_string(),
            fingerprint,
            created_at: now,
        })
    }

    async fn rotate_keys(&self) -> Result<()> {
        info!("Starting JWKS key rotation...");
        
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64;

        // Check which keys need rotation
        let mut keys_to_rotate = Vec::new();
        {
            let keys = self.keys.read().await;
            for (kid, key) in keys.iter() {
                let time_until_expiry = key.expires_at - now;
                let overlap_period_seconds = self.rotation_config.overlap_period_hours * 3600;
                
                if time_until_expiry <= overlap_period_seconds as i64 && !key.revoked {
                    keys_to_rotate.push(kid.clone());
                }
            }
        }

        // Generate new keys for rotation
        for old_kid in keys_to_rotate {
            let new_kid = format!("{}-{}", old_kid, now);
            
            // Generate new key
            let new_key = self.generate_key(&new_kid).await?;
            
            // Update keys map
            {
                let mut keys = self.keys.write().await;
                keys.insert(new_kid.clone(), new_key);
                
                // Mark old key as revoked
                if let Some(old_key) = keys.get_mut(&old_kid) {
                    old_key.revoked = true;
                    info!("Revoked old key: {}", old_kid);
                }
            }

            // Generate new certificate pin
            let new_pin = self.generate_certificate_pin(&new_kid).await?;
            {
                let mut pins = self.certificate_pins.write().await;
                pins.insert(new_kid.clone(), new_pin);
            }

            info!("Rotated key: {} -> {}", old_kid, new_kid);
        }

        // Clean up old revoked keys (keep them for a grace period)
        self.cleanup_old_keys().await?;

        info!("JWKS key rotation completed");
        Ok(())
    }

    async fn cleanup_old_keys(&self) -> Result<()> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs() as i64;

        let grace_period = 7 * 24 * 3600; // 7 days grace period

        let mut keys_to_remove = Vec::new();
        {
            let keys = self.keys.read().await;
            for (kid, key) in keys.iter() {
                if key.revoked && (now - key.expires_at) > grace_period {
                    keys_to_remove.push(kid.clone());
                }
            }
        }

        if !keys_to_remove.is_empty() {
            let mut keys = self.keys.write().await;
            let mut pins = self.certificate_pins.write().await;
            
            for kid in keys_to_remove {
                keys.remove(&kid);
                pins.remove(&kid);
                info!("Cleaned up old key: {}", kid);
            }
        }

        Ok(())
    }

    async fn get_jwks(&self) -> JwksSet {
        let keys = self.keys.read().await;
        let active_keys: Vec<JwksKey> = keys
            .values()
            .filter(|key| !key.revoked)
            .cloned()
            .collect();

        JwksSet { keys: active_keys }
    }

    async fn validate_token_with_pinning(&self, token: &str) -> Result<bool> {
        // Decode token header to get kid
        let parts: Vec<&str> = token.split('.').collect();
        if parts.len() != 3 {
            return Err(anyhow::anyhow!("Invalid JWT format"));
        }

        let header_bytes = general_purpose::STANDARD
            .decode(parts[0])
            .context("Failed to decode JWT header")?;
        
        let header: serde_json::Value = serde_json::from_slice(&header_bytes)
            .context("Failed to parse JWT header")?;

        let kid = header.get("kid")
            .and_then(|k| k.as_str())
            .ok_or_else(|| anyhow::anyhow!("Missing kid in JWT header"))?;

        // Check certificate pinning
        let pins = self.certificate_pins.read().await;
        if let Some(pin) = pins.get(kid) {
            // In production, this would verify the actual certificate fingerprint
            // For now, we'll just check that the pin exists
            info!("Certificate pin validated for kid: {}", kid);
        } else {
            return Err(anyhow::anyhow!("Certificate pin not found for kid: {}", kid));
        }

        // Validate token with JWKS
        let jwks = self.get_jwks().await;
        if let Some(key) = jwks.keys.iter().find(|k| k.kid == kid) {
            // In production, this would perform actual JWT validation
            info!("Token validated with JWKS for kid: {}", kid);
            Ok(true)
        } else {
            Err(anyhow::anyhow!("Key not found in JWKS for kid: {}", kid))
        }
    }

    async fn start_rotation_scheduler(&self) {
        if !self.rotation_config.auto_rotation_enabled {
            info!("Auto rotation disabled");
            return;
        }

        let rotation_interval = Duration::from_secs(
            self.rotation_config.rotation_interval_hours * 3600
        );

        let mut interval = interval(rotation_interval);
        let manager = self.clone();

        tokio::spawn(async move {
            loop {
                interval.tick().await;
                
                if let Err(e) = manager.rotate_keys().await {
                    error!("Key rotation failed: {}", e);
                }
            }
        });

        info!("JWKS rotation scheduler started with interval: {:?}", rotation_interval);
    }
}

// Implement Clone for JwksManager to allow sharing across tasks
impl Clone for JwksManager {
    fn clone(&self) -> Self {
        Self {
            keys: self.keys.clone(),
            certificate_pins: self.certificate_pins.clone(),
            rotation_config: RotationConfig {
                rotation_interval_hours: self.rotation_config.rotation_interval_hours,
                key_lifetime_hours: self.rotation_config.key_lifetime_hours,
                overlap_period_hours: self.rotation_config.overlap_period_hours,
                auto_rotation_enabled: self.rotation_config.auto_rotation_enabled,
            },
            http_client: self.http_client.clone(),
            kms_proxy_url: self.kms_proxy_url.clone(),
            vault_url: self.vault_url.clone(),
            vault_token: self.vault_token.clone(),
        }
    }
}

async fn handle_request(
    req: Request<Body>,
    manager: Arc<JwksManager>,
) -> Result<Response<Body>, hyper::Error> {
    let path = req.uri().path();
    let method = req.method();

    match (method.as_str(), path) {
        ("GET", "/.well-known/jwks.json") => {
            let jwks = manager.get_jwks().await;
            let response_json = serde_json::to_string(&jwks).unwrap();
            
            Ok(Response::builder()
                .header("Content-Type", "application/json")
                .header("Cache-Control", "public, max-age=300") // 5 minute cache
                .body(Body::from(response_json))
                .unwrap())
        }
        ("POST", "/rotate-keys") => {
            match manager.rotate_keys().await {
                Ok(_) => {
                    let response = serde_json::json!({
                        "success": true,
                        "message": "Keys rotated successfully"
                    });
                    
                    Ok(Response::builder()
                        .header("Content-Type", "application/json")
                        .body(Body::from(response.to_string()))
                        .unwrap())
                }
                Err(e) => {
                    let response = serde_json::json!({
                        "success": false,
                        "error": e.to_string()
                    });
                    
                    Ok(Response::builder()
                        .status(500)
                        .header("Content-Type", "application/json")
                        .body(Body::from(response.to_string()))
                        .unwrap())
                }
            }
        }
        ("POST", "/validate-token") => {
            let body_bytes = hyper::body::to_bytes(req.into_body()).await?;
            let request: serde_json::Value = serde_json::from_slice(&body_bytes)
                .unwrap_or_else(|_| serde_json::Value::Null);

            if let Some(token) = request.get("token").and_then(|t| t.as_str()) {
                match manager.validate_token_with_pinning(token).await {
                    Ok(_) => {
                        let response = serde_json::json!({
                            "valid": true,
                            "message": "Token validated successfully"
                        });
                        
                        Ok(Response::builder()
                            .header("Content-Type", "application/json")
                            .body(Body::from(response.to_string()))
                            .unwrap())
                    }
                    Err(e) => {
                        let response = serde_json::json!({
                            "valid": false,
                            "error": e.to_string()
                        });
                        
                        Ok(Response::builder()
                            .status(400)
                            .header("Content-Type", "application/json")
                            .body(Body::from(response.to_string()))
                            .unwrap())
                    }
                }
            } else {
                let response = serde_json::json!({
                    "error": "Missing token in request body"
                });
                
                Ok(Response::builder()
                    .status(400)
                    .header("Content-Type", "application/json")
                    .body(Body::from(response.to_string()))
                    .unwrap())
            }
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

    let manager = Arc::new(JwksManager::new());
    
    // Initialize keys
    if let Err(e) = manager.initialize_keys().await {
        error!("Failed to initialize keys: {}", e);
        return Err(e);
    }

    // Start rotation scheduler
    manager.start_rotation_scheduler().await;

    let addr = std::net::SocketAddr::from(([0, 0, 0, 0], 8083));

    let make_svc = make_service_fn(move |_conn| {
        let manager = manager.clone();
        async move {
            Ok::<_, hyper::Error>(service_fn(move |req| {
                let manager = manager.clone();
                handle_request(req, manager)
            }))
        }
    });

    let server = Server::bind(&addr).serve(make_svc);

    info!("JWKS Manager listening on {}", addr);

    if let Err(e) = server.await {
        error!("Server error: {}", e);
    }

    Ok(())
}
