use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use uuid::Uuid;

/// Capability token verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TokenValidationResult {
    Valid {
        subject_id: String,
        capabilities: Vec<String>,
        expires_at: u64,
    },
    Invalid {
        reason: String,
    },
    Expired {
        expires_at: u64,
    },
}

/// Token cache entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenCacheEntry {
    pub token_id: String,
    pub subject_id: String,
    pub capabilities: Vec<String>,
    pub expires_at: u64,
    pub cached_at: u64,
}

/// Capability token verifier
pub struct CapabilityVerifier {
    cache: RwLock<HashMap<String, TokenCacheEntry>>,
    signing_keys: RwLock<HashMap<String, Vec<u8>>>,
    cache_ttl: u64,
}

impl CapabilityVerifier {
    pub fn new(cache_ttl: u64) -> Self {
        Self {
            cache: RwLock::new(HashMap::new()),
            signing_keys: RwLock::new(HashMap::new()),
            cache_ttl,
        }
    }

    /// Add a signing key
    pub async fn add_signing_key(&self, key_id: String, public_key: Vec<u8>) {
        let mut keys = self.signing_keys.write().await;
        keys.insert(key_id, public_key);
    }

    /// Verify a capability token
    pub async fn verify_token(&self, token_data: &[u8]) -> TokenValidationResult {
        // Parse token (simplified - in real implementation would use DSSE)
        let token = match self.parse_token(token_data) {
            Ok(token) => token,
            Err(e) => return TokenValidationResult::Invalid {
                reason: format!("Failed to parse token: {}", e),
            },
        };

        // Check cache first
        if let Some(cached) = self.get_cached_token(&token.token_id).await {
            let now = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();

            if now > cached.expires_at {
                return TokenValidationResult::Expired {
                    expires_at: cached.expires_at,
                };
            }

            return TokenValidationResult::Valid {
                subject_id: cached.subject_id,
                capabilities: cached.capabilities,
                expires_at: cached.expires_at,
            };
        }

        // Verify signature
        if !self.verify_signature(&token).await {
            return TokenValidationResult::Invalid {
                reason: "Invalid signature".to_string(),
            };
        }

        // Check expiration
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if now > token.expires_at {
            return TokenValidationResult::Expired {
                expires_at: token.expires_at,
            };
        }

        // Cache valid token
        let cache_entry = TokenCacheEntry {
            token_id: token.token_id.clone(),
            subject_id: token.subject_id.clone(),
            capabilities: token.capabilities.clone(),
            expires_at: token.expires_at,
            cached_at: now,
        };

        self.cache_token(cache_entry).await;

        TokenValidationResult::Valid {
            subject_id: token.subject_id,
            capabilities: token.capabilities,
            expires_at: token.expires_at,
        }
    }

    /// Check if subject has required capabilities
    pub async fn has_capabilities(
        &self,
        token_data: &[u8],
        required_capabilities: &[String],
    ) -> bool {
        match self.verify_token(token_data).await {
            TokenValidationResult::Valid { capabilities, .. } => {
                required_capabilities.iter().all(|cap| capabilities.contains(cap))
            }
            _ => false,
        }
    }

    /// Get cached token
    async fn get_cached_token(&self, token_id: &str) -> Option<TokenCacheEntry> {
        let cache = self.cache.read().await;
        cache.get(token_id).cloned()
    }

    /// Cache token
    async fn cache_token(&self, entry: TokenCacheEntry) {
        let mut cache = self.cache.write().await;
        cache.insert(entry.token_id.clone(), entry);
    }

    /// Parse token (simplified implementation)
    fn parse_token(&self, token_data: &[u8]) -> Result<ParsedToken, String> {
        // In real implementation, this would parse DSSE envelope
        // For now, we'll use a simplified JSON format
        let token_str = String::from_utf8(token_data.to_vec())
            .map_err(|e| format!("Invalid UTF-8: {}", e))?;

        let parsed: serde_json::Value = serde_json::from_str(&token_str)
            .map_err(|e| format!("Invalid JSON: {}", e))?;

        let token_id = parsed["token_id"]
            .as_str()
            .ok_or("Missing token_id")?
            .to_string();

        let subject_id = parsed["subject_id"]
            .as_str()
            .ok_or("Missing subject_id")?
            .to_string();

        let capabilities = parsed["capabilities"]
            .as_array()
            .ok_or("Missing capabilities")?
            .iter()
            .filter_map(|v| v.as_str().map(|s| s.to_string()))
            .collect();

        let expires_at = parsed["expires_at"]
            .as_u64()
            .ok_or("Missing expires_at")?;

        Ok(ParsedToken {
            token_id,
            subject_id,
            capabilities,
            expires_at,
        })
    }

    /// Verify signature (simplified implementation)
    async fn verify_signature(&self, _token: &ParsedToken) -> bool {
        // In real implementation, this would verify DSSE signature
        // For now, we'll assume valid if we can parse it
        true
    }

    /// Clean expired tokens from cache
    pub async fn clean_expired_tokens(&self) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut cache = self.cache.write().await;
        cache.retain(|_, entry| {
            entry.expires_at > now && (now - entry.cached_at) < self.cache_ttl
        });
    }

    /// Get cache statistics
    pub async fn get_cache_stats(&self) -> CacheStats {
        let cache = self.cache.read().await;
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let total_tokens = cache.len();
        let expired_tokens = cache
            .values()
            .filter(|entry| entry.expires_at <= now)
            .count();

        CacheStats {
            total_tokens,
            expired_tokens,
            cache_ttl: self.cache_ttl,
        }
    }
}

/// Parsed token structure
#[derive(Debug, Clone)]
struct ParsedToken {
    token_id: String,
    subject_id: String,
    capabilities: Vec<String>,
    expires_at: u64,
}

/// Cache statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    pub total_tokens: usize,
    pub expired_tokens: usize,
    pub cache_ttl: u64,
}

/// Capability manager for the sidecar watcher
pub struct CapabilityManager {
    verifier: CapabilityVerifier,
}

impl CapabilityManager {
    pub fn new(verifier: CapabilityVerifier) -> Self {
        Self { verifier }
    }

    /// Verify token and check capabilities
    pub async fn verify_capabilities(
        &self,
        token_data: &[u8],
        required_capabilities: &[String],
    ) -> Result<bool, String> {
        if self.verifier.has_capabilities(token_data, required_capabilities).await {
            Ok(true)
        } else {
            Err("Insufficient capabilities".to_string())
        }
    }

    /// Get token subject ID
    pub async fn get_token_subject(&self, token_data: &[u8]) -> Result<String, String> {
        match self.verifier.verify_token(token_data).await {
            TokenValidationResult::Valid { subject_id, .. } => Ok(subject_id),
            TokenValidationResult::Invalid { reason } => Err(reason),
            TokenValidationResult::Expired { .. } => Err("Token expired".to_string()),
        }
    }

    /// Get token capabilities
    pub async fn get_token_capabilities(
        &self,
        token_data: &[u8],
    ) -> Result<Vec<String>, String> {
        match self.verifier.verify_token(token_data).await {
            TokenValidationResult::Valid { capabilities, .. } => Ok(capabilities),
            TokenValidationResult::Invalid { reason } => Err(reason),
            TokenValidationResult::Expired { .. } => Err("Token expired".to_string()),
        }
    }

    /// Clean expired tokens
    pub async fn clean_expired_tokens(&self) {
        self.verifier.clean_expired_tokens().await;
    }

    /// Get cache statistics
    pub async fn get_cache_stats(&self) -> CacheStats {
        self.verifier.get_cache_stats().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_token_verification() {
        let verifier = CapabilityVerifier::new(3600);
        let manager = CapabilityManager::new(verifier);

        // Create a test token
        let token_data = r#"{
            "token_id": "test_token_123",
            "subject_id": "user_456",
            "capabilities": ["read_docs", "send_email"],
            "expires_at": 9999999999
        }"#;

        let result = manager
            .verify_capabilities(
                token_data.as_bytes(),
                &["read_docs".to_string()],
            )
            .await;

        assert!(result.is_ok());
        assert!(result.unwrap());
    }

    #[tokio::test]
    async fn test_missing_capability() {
        let verifier = CapabilityVerifier::new(3600);
        let manager = CapabilityManager::new(verifier);

        let token_data = r#"{
            "token_id": "test_token_123",
            "subject_id": "user_456",
            "capabilities": ["read_docs"],
            "expires_at": 9999999999
        }"#;

        let result = manager
            .verify_capabilities(
                token_data.as_bytes(),
                &["send_email".to_string()],
            )
            .await;

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Insufficient capabilities");
    }

    #[tokio::test]
    async fn test_expired_token() {
        let verifier = CapabilityVerifier::new(3600);
        let manager = CapabilityManager::new(verifier);

        let token_data = r#"{
            "token_id": "test_token_123",
            "subject_id": "user_456",
            "capabilities": ["read_docs"],
            "expires_at": 0
        }"#;

        let result = manager
            .verify_capabilities(
                token_data.as_bytes(),
                &["read_docs".to_string()],
            )
            .await;

        assert!(result.is_err());
    }
} 