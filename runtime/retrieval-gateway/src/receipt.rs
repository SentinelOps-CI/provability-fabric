use anyhow::{Context, Result};
use base64::{engine::general_purpose::STANDARD as B64_STD, Engine as _};
use ed25519_dalek::pkcs8::DecodePrivateKey;
use ed25519_dalek::{Signer, SigningKey};
use pf_dsse::verify::{canonical_receipt_payload, EnvelopeSignature};
use pf_dsse::{
    verify_access_receipt, AccessReceiptPayload, Envelope, ACCESS_RECEIPT_TYPE,
};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// Access receipt for retrieval queries (wire format matches ledger schema).
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
    pub sign_alg: String,
    pub sig: String,
}

impl AccessReceipt {
    fn to_payload(&self) -> AccessReceiptPayload {
        AccessReceiptPayload {
            receipt_id: self.receipt_id.clone(),
            tenant: self.tenant.clone(),
            subject_id: self.subject_id.clone(),
            query_hash: self.query_hash.clone(),
            index_shard: self.index_shard.clone(),
            timestamp: self.timestamp as i64,
            result_hash: self.result_hash.clone(),
            result_count: self.result_count as i32,
            query_time_ms: self.query_time_ms as i32,
            signature: String::new(),
        }
    }
}

fn load_signing_key_from_env() -> Result<SigningKey> {
    if let Ok(b64) = std::env::var("RECEIPT_SIGNING_KEY") {
        let bytes = B64_STD
            .decode(b64.trim())
            .context("RECEIPT_SIGNING_KEY: invalid base64")?;
        if bytes.len() == 32 {
            let seed: [u8; 32] = bytes
                .try_into()
                .map_err(|_| anyhow::anyhow!("RECEIPT_SIGNING_KEY must be 32 bytes"))?;
            return Ok(SigningKey::from_bytes(&seed));
        }
        anyhow::bail!("RECEIPT_SIGNING_KEY must be 32 bytes (base64)");
    }

    if let Ok(path) = std::env::var("RECEIPT_SIGNING_KEY_PATH") {
        return load_signing_key_from_path(&path);
    }

    anyhow::bail!("set RECEIPT_SIGNING_KEY (base64) or RECEIPT_SIGNING_KEY_PATH");
}

fn load_signing_key_from_path(path: &str) -> Result<SigningKey> {
    let raw = fs::read(path).context("RECEIPT_SIGNING_KEY_PATH: failed to read file")?;
    if raw.starts_with(b"-----BEGIN") {
        let pem_str = std::str::from_utf8(&raw)
            .context("RECEIPT_SIGNING_KEY_PATH: invalid PEM utf-8")?;
        return SigningKey::from_pkcs8_der(pem::parse(pem_str)?.contents())
            .map_err(|e| anyhow::anyhow!("RECEIPT_SIGNING_KEY_PATH: invalid PEM key: {e}"));
    }
    if raw.len() == 32 {
        let seed: [u8; 32] = raw
            .try_into()
            .map_err(|_| anyhow::anyhow!("RECEIPT_SIGNING_KEY_PATH: expected 32 raw bytes"))?;
        return Ok(SigningKey::from_bytes(&seed));
    }
    anyhow::bail!("RECEIPT_SIGNING_KEY_PATH: file must be 32 raw bytes or PEM private key");
}

/// Receipt signer using pf-dsse canonical payload + Ed25519.
pub struct ReceiptSigner {
    signing_key: SigningKey,
    key_id: String,
}

impl ReceiptSigner {
    /// Create new receipt signer from env (`RECEIPT_SIGNING_KEY` or `RECEIPT_SIGNING_KEY_PATH`).
    pub async fn new() -> Result<Self> {
        let signing_key = load_signing_key_from_env()
            .context("RECEIPT_SIGNING_KEY or RECEIPT_SIGNING_KEY_PATH must be set")?;
        let key_id =
            std::env::var("RECEIPT_SIGNING_KEY_ID").unwrap_or_else(|_| "receipt_signer_v1".to_string());

        Ok(Self {
            signing_key,
            key_id,
        })
    }

    /// Sign a receipt with Ed25519 over the pf-dsse canonical payload.
    pub async fn sign_receipt(&self, receipt: &AccessReceipt) -> Result<AccessReceipt> {
        let payload = receipt.to_payload();
        let canonical = canonical_receipt_payload(&payload)
            .map_err(|e| anyhow::anyhow!("canonical receipt payload: {e}"))?;
        let signature = self.signing_key.sign(&canonical);
        let mut signed = receipt.clone();
        signed.sign_alg = "ed25519".to_string();
        signed.sig = B64_STD.encode(signature.to_bytes());
        Ok(signed)
    }

    /// Build a DSSE envelope for the receipt (cross-language verification contract).
    pub fn dsse_envelope(&self, receipt: &AccessReceipt) -> Result<Envelope> {
        let payload = receipt.to_payload();
        let canonical = canonical_receipt_payload(&payload)
            .map_err(|e| anyhow::anyhow!("canonical receipt payload: {e}"))?;
        let signature = self.signing_key.sign(&canonical);
        Ok(Envelope {
            payload_type: ACCESS_RECEIPT_TYPE.to_string(),
            payload: B64_STD.encode(&canonical),
            signatures: vec![EnvelopeSignature {
                keyid: self.key_id.clone(),
                sig: B64_STD.encode(signature.to_bytes()),
                alg: "ed25519".to_string(),
            }],
        })
    }

    /// Verify receipt signature via pf-dsse.
    pub fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<bool> {
        if receipt.sig.is_empty() {
            return Ok(false);
        }
        let payload = receipt.to_payload();
        match verify_access_receipt(&payload, &receipt.sign_alg, &receipt.sig) {
            Ok(()) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}

/// Receipt validator for external verification.
pub struct ReceiptValidator;

impl ReceiptValidator {
    /// Validate receipt structure and DSSE signature when enforcement is enabled.
    pub async fn validate_receipt(receipt: &AccessReceipt) -> Result<bool> {
        if receipt.receipt_id.is_empty()
            || receipt.tenant.is_empty()
            || receipt.subject_id.is_empty()
            || receipt.query_hash.len() != 64
            || receipt.result_hash.len() != 64
        {
            return Ok(false);
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if receipt.timestamp > now + 300 || receipt.timestamp < now.saturating_sub(86400) {
            return Ok(false);
        }

        if receipt.sig.is_empty() || receipt.sign_alg != "ed25519" {
            return Ok(false);
        }

        let payload = receipt.to_payload();
        Ok(verify_access_receipt(&payload, &receipt.sign_alg, &receipt.sig).is_ok())
    }
}

pub fn crypto_fixtures_dir() -> PathBuf {
    let candidates = [
        PathBuf::from("tests/fixtures/crypto"),
        PathBuf::from("../../tests/fixtures/crypto"),
        PathBuf::from("../../../tests/fixtures/crypto"),
    ];
    for candidate in candidates {
        if candidate.join("ed25519_public.pem").exists() {
            return candidate;
        }
    }
    panic!("crypto fixtures not found under tests/fixtures/crypto");
}

fn set_test_signing_env(fixtures: &Path) {
    std::env::set_var(
        "RECEIPT_SIGNING_KEY_PATH",
        fixtures.join("ed25519_private.pem"),
    );
    std::env::set_var("PF_TRUST_ROOT_PEM", fixtures.join("ed25519_public.pem"));
    std::env::set_var("PF_ENFORCE_DSSE", "1");
}

#[cfg(test)]
mod tests {
    use super::*;
    use pf_dsse::verify_envelope;
    use std::fs;

    fn sample_receipt() -> AccessReceipt {
        AccessReceipt {
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
            sign_alg: String::new(),
            sig: String::new(),
        }
    }

    #[tokio::test]
    async fn test_receipt_signing_with_fixture_keys() {
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);

        let signer = ReceiptSigner::new().await.unwrap();
        let receipt = sample_receipt();
        let signed = signer.sign_receipt(&receipt).await.unwrap();

        assert_eq!(signed.sign_alg, "ed25519");
        assert!(!signed.sig.is_empty());
        assert!(signer.verify_receipt(&signed).unwrap());

        let envelope = signer.dsse_envelope(&signed).unwrap();
        let result = verify_envelope(&envelope, ACCESS_RECEIPT_TYPE);
        assert!(result.valid, "{:?}", result.reason);
    }

    #[tokio::test]
    async fn test_fixture_envelope_verifies() {
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);

        let env_data = fs::read_to_string(fixtures.join("dsse_sample_envelope.json")).unwrap();
        let envelope: Envelope = serde_json::from_str(&env_data).unwrap();
        let result = verify_envelope(&envelope, ACCESS_RECEIPT_TYPE);
        assert!(result.valid, "{:?}", result.reason);
    }

    #[tokio::test]
    async fn test_receipt_validation() {
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);

        let signer = ReceiptSigner::new().await.unwrap();
        let signed = signer.sign_receipt(&sample_receipt()).await.unwrap();
        assert!(ReceiptValidator::validate_receipt(&signed).await.unwrap());

        let mut invalid = signed.clone();
        invalid.tenant = String::new();
        assert!(!ReceiptValidator::validate_receipt(&invalid).await.unwrap());
    }
}
