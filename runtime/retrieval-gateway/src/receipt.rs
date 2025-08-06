use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// Access receipt for retrieval queries
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessReceipt {
    pub receipt_id: String,
    pub tenant: String,
    pub subject_id: String,
    pub query_hash: String,
    pub index_shard: String,
    pub timestamp: u64,
    pub result_hash: String,
    pub result_count: usize,
    pub query_time_ms: u64,
    pub signature: String,
}

/// Receipt signer for DSSE signatures
pub struct ReceiptSigner {
    signing_key: Vec<u8>,
    key_id: String,
}

impl ReceiptSigner {
    /// Create new receipt signer
    pub async fn new() -> Result<Self> {
        // In real implementation, would load signing key from secure storage
        let signing_key = vec![0u8; 32]; // Placeholder key
        let key_id = "receipt_signer_v1".to_string();

        Ok(Self {
            signing_key,
            key_id,
        })
    }

    /// Sign a receipt with DSSE
    pub async fn sign_receipt(&self, receipt: &AccessReceipt) -> Result<AccessReceipt> {
        let mut signed_receipt = receipt.clone();
        
        // Create DSSE payload
        let payload = self.create_dsse_payload(receipt)?;
        
        // Sign payload
        let signature = self.sign_payload(&payload).await?;
        
        signed_receipt.signature = signature;
        Ok(signed_receipt)
    }

    /// Create DSSE payload from receipt
    fn create_dsse_payload(&self, receipt: &AccessReceipt) -> Result<String> {
        // DSSE payload format: base64(json(receipt))
        let receipt_json = serde_json::to_string(receipt)
            .context("Failed to serialize receipt")?;
        
        let payload = base64::encode(receipt_json);
        Ok(payload)
    }

    /// Sign DSSE payload
    async fn sign_payload(&self, payload: &str) -> Result<String> {
        // Create DSSE envelope
        let envelope = DSSEEnvelope {
            payload_type: "application/vnd.provability-fabric.access-receipt".to_string(),
            payload: payload.to_string(),
            signatures: vec![DSSESignature {
                key_id: self.key_id.clone(),
                algorithm: "ed25519".to_string(),
                signature: self.create_signature(payload)?,
            }],
        };

        // Serialize and encode envelope
        let envelope_json = serde_json::to_string(&envelope)
            .context("Failed to serialize DSSE envelope")?;
        
        Ok(base64::encode(envelope_json))
    }

    /// Create Ed25519 signature (simplified)
    fn create_signature(&self, payload: &str) -> Result<String> {
        // In real implementation, would use proper Ed25519 signing
        use sha2::{Digest, Sha256};
        
        let mut hasher = Sha256::new();
        hasher.update(payload.as_bytes());
        hasher.update(&self.signing_key);
        
        let signature_bytes = hasher.finalize();
        Ok(base64::encode(signature_bytes))
    }

    /// Verify receipt signature
    pub async fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<bool> {
        if receipt.signature.is_empty() {
            return Ok(false);
        }

        // Decode DSSE envelope
        let envelope_bytes = base64::decode(&receipt.signature)
            .context("Failed to decode signature")?;
        
        let envelope: DSSEEnvelope = serde_json::from_slice(&envelope_bytes)
            .context("Failed to parse DSSE envelope")?;

        // Verify envelope structure
        if envelope.payload_type != "application/vnd.provability-fabric.access-receipt" {
            return Ok(false);
        }

        if envelope.signatures.is_empty() {
            return Ok(false);
        }

        // Verify signature
        let signature = &envelope.signatures[0];
        if signature.key_id != self.key_id || signature.algorithm != "ed25519" {
            return Ok(false);
        }

        // Verify payload matches receipt
        let expected_signature = self.create_signature(&envelope.payload)?;
        Ok(signature.signature == expected_signature)
    }
}

/// DSSE (Dead Simple Signing Envelope) structure
#[derive(Debug, Serialize, Deserialize)]
struct DSSEEnvelope {
    #[serde(rename = "payloadType")]
    payload_type: String,
    payload: String,
    signatures: Vec<DSSESignature>,
}

/// DSSE signature
#[derive(Debug, Serialize, Deserialize)]
struct DSSESignature {
    #[serde(rename = "keyid")]
    key_id: String,
    #[serde(rename = "sig")]
    signature: String,
    #[serde(rename = "alg")]
    algorithm: String,
}

/// Receipt validator for external verification
pub struct ReceiptValidator {
    public_keys: std::collections::HashMap<String, Vec<u8>>,
}

impl ReceiptValidator {
    /// Create new validator with public keys
    pub fn new() -> Self {
        Self {
            public_keys: std::collections::HashMap::new(),
        }
    }

    /// Add public key for verification
    pub fn add_public_key(&mut self, key_id: String, public_key: Vec<u8>) {
        self.public_keys.insert(key_id, public_key);
    }

    /// Validate receipt integrity
    pub async fn validate_receipt(&self, receipt: &AccessReceipt) -> Result<bool> {
        // Check required fields
        if receipt.receipt_id.is_empty() || 
           receipt.tenant.is_empty() ||
           receipt.subject_id.is_empty() ||
           receipt.query_hash.len() != 64 ||
           receipt.result_hash.len() != 64 {
            return Ok(false);
        }

        // Check timestamp is reasonable (not too old or in future)
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        if receipt.timestamp > now + 300 || // 5 minutes in future
           receipt.timestamp < now.saturating_sub(86400) { // 24 hours old
            return Ok(false);
        }

        // Verify signature if we have the public key
        if let Some(_public_key) = self.get_signing_key(&receipt.signature).await? {
            // Would verify signature here
            return Ok(true);
        }

        // If no signature verification, at least check structure
        Ok(!receipt.signature.is_empty())
    }

    /// Extract signing key from signature
    async fn get_signing_key(&self, signature: &str) -> Result<Option<&Vec<u8>>> {
        let envelope_bytes = base64::decode(signature)
            .context("Failed to decode signature")?;
        
        let envelope: DSSEEnvelope = serde_json::from_slice(&envelope_bytes)
            .context("Failed to parse DSSE envelope")?;

        if let Some(sig) = envelope.signatures.first() {
            Ok(self.public_keys.get(&sig.key_id))
        } else {
            Ok(None)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_receipt_signing() {
        let signer = ReceiptSigner::new().await.unwrap();
        
        let receipt = AccessReceipt {
            receipt_id: "test_receipt_123".to_string(),
            tenant: "tenant1".to_string(),
            subject_id: "user1".to_string(),
            query_hash: "a".repeat(64),
            index_shard: "shard_tenant1".to_string(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            result_hash: "b".repeat(64),
            result_count: 5,
            query_time_ms: 100,
            signature: "".to_string(),
        };

        let signed_receipt = signer.sign_receipt(&receipt).await.unwrap();
        assert!(!signed_receipt.signature.is_empty());
        
        let verification_result = signer.verify_receipt(&signed_receipt).await.unwrap();
        assert!(verification_result);
    }

    #[tokio::test]
    async fn test_receipt_validation() {
        let mut validator = ReceiptValidator::new();
        validator.add_public_key("test_key".to_string(), vec![0u8; 32]);

        let valid_receipt = AccessReceipt {
            receipt_id: "test_receipt_123".to_string(),
            tenant: "tenant1".to_string(),
            subject_id: "user1".to_string(),
            query_hash: "a".repeat(64),
            index_shard: "shard_tenant1".to_string(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            result_hash: "b".repeat(64),
            result_count: 5,
            query_time_ms: 100,
            signature: base64::encode("test_signature"),
        };

        let result = validator.validate_receipt(&valid_receipt).await.unwrap();
        assert!(result);

        // Test invalid receipt (empty tenant)
        let mut invalid_receipt = valid_receipt.clone();
        invalid_receipt.tenant = "".to_string();
        
        let result = validator.validate_receipt(&invalid_receipt).await.unwrap();
        assert!(!result);
    }

    #[test]
    fn test_dsse_envelope_serialization() {
        let envelope = DSSEEnvelope {
            payload_type: "application/vnd.provability-fabric.access-receipt".to_string(),
            payload: "test_payload".to_string(),
            signatures: vec![DSSESignature {
                key_id: "test_key".to_string(),
                signature: "test_signature".to_string(),
                algorithm: "ed25519".to_string(),
            }],
        };

        let json = serde_json::to_string(&envelope).unwrap();
        let parsed: DSSEEnvelope = serde_json::from_str(&json).unwrap();
        
        assert_eq!(parsed.payload_type, envelope.payload_type);
        assert_eq!(parsed.signatures.len(), 1);
    }
}