use anyhow::{Context, Result};
use crate::result_commitment::valid_result_hash;
use base64::{engine::general_purpose::STANDARD as B64_STD, Engine as _};
use ed25519_dalek::pkcs8::DecodePrivateKey;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier};
use pf_dsse::verify::{canonical_receipt_payload, verify_envelope, EnvelopeSignature};
use pf_dsse::{
    AccessReceiptPayload, Envelope, ACCESS_RECEIPT_TYPE,
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
    // Reject values not exactly representable by the signed payload's integer types.
    fn to_payload(&self) -> Result<AccessReceiptPayload> {
        Ok(AccessReceiptPayload {
            receipt_id: self.receipt_id.clone(),
            tenant: self.tenant.clone(),
            subject_id: self.subject_id.clone(),
            query_hash: self.query_hash.clone(),
            index_shard: self.index_shard.clone(),
            timestamp: i64::try_from(self.timestamp).context("receipt timestamp exceeds i64")?,
            result_hash: self.result_hash.clone(),
            result_count: i32::try_from(self.result_count).context("receipt result_count exceeds i32")?,
            query_time_ms: i32::try_from(self.query_time_ms).context("receipt query_time_ms exceeds i32")?,
            signature: String::new(),
        })
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
        let payload = receipt.to_payload()?;
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
        let payload = receipt.to_payload()?;
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

    /// Check a receipt against this signer's own Ed25519 public key.
    ///
    /// This local consistency check is independent of the ambient DSSE opt-out
    /// flag. External provenance still needs a separately trusted public key.
    pub fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<bool> {
        if receipt.sign_alg != "ed25519" {
            return Ok(false);
        }
        let signature_bytes = match B64_STD.decode(&receipt.sig) {
            Ok(bytes) => bytes,
            Err(_) => return Ok(false),
        };
        let signature_bytes: [u8; 64] = match signature_bytes.try_into() {
            Ok(bytes) => bytes,
            Err(_) => return Ok(false),
        };
        let payload = match receipt.to_payload() {
            Ok(payload) => payload,
            Err(_) => return Ok(false),
        };
        let canonical = canonical_receipt_payload(&payload)
            .map_err(|e| anyhow::anyhow!("canonical receipt payload: {e}"))?;
        let signature = Signature::from_bytes(&signature_bytes);
        Ok(self.signing_key.verifying_key().verify(&canonical, &signature).is_ok())
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
            || !valid_result_hash(&receipt.result_hash)
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

        let payload = match receipt.to_payload() {
            Ok(payload) => payload,
            Err(_) => return Ok(false),
        };
        let canonical = canonical_receipt_payload(&payload)
            .map_err(|e| anyhow::anyhow!("canonical receipt payload: {e}"))?;
        // verify_envelope always verifies against PF_TRUST_ROOT_PEM. The
        // structural-only PF_ENFORCE_DSSE=0 mode must not assert validity
        // at this external receipt-verification boundary.
        let envelope = Envelope {
            payload_type: ACCESS_RECEIPT_TYPE.to_string(),
            payload: B64_STD.encode(canonical),
            signatures: vec![EnvelopeSignature {
                keyid: String::new(),
                sig: receipt.sig.clone(),
                alg: receipt.sign_alg.clone(),
            }],
        };
        Ok(verify_envelope(&envelope, ACCESS_RECEIPT_TYPE).valid)
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
    use std::fs;
    use std::sync::Mutex;

    // These fixture tests modify process-wide environment variables.
    static RECEIPT_TEST_ENV: Mutex<()> = Mutex::new(());

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
        let _env_guard = RECEIPT_TEST_ENV.lock().unwrap_or_else(|e| e.into_inner());
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
        let _env_guard = RECEIPT_TEST_ENV.lock().unwrap_or_else(|e| e.into_inner());
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);

        let env_data = fs::read_to_string(fixtures.join("dsse_sample_envelope.json")).unwrap();
        let envelope: Envelope = serde_json::from_str(&env_data).unwrap();
        let result = verify_envelope(&envelope, ACCESS_RECEIPT_TYPE);
        assert!(result.valid, "{:?}", result.reason);
    }

    #[tokio::test]
    async fn test_receipt_validation() {
        let _env_guard = RECEIPT_TEST_ENV.lock().unwrap_or_else(|e| e.into_inner());
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);

        let signer = ReceiptSigner::new().await.unwrap();
        let signed = signer.sign_receipt(&sample_receipt()).await.unwrap();
        assert!(ReceiptValidator::validate_receipt(&signed).await.unwrap());

        let mut invalid = signed.clone();
        invalid.tenant = String::new();
        assert!(!ReceiptValidator::validate_receipt(&invalid).await.unwrap());

        // Legacy SHA-256 receipts remain structurally recognized under v1.
        assert!(valid_result_hash(&signed.result_hash));

        // A v2 marker is included in the signed field, not interpreted as v1.
        let mut v2 = sample_receipt();
        v2.result_hash = format!("sha256-v2:{}", "a".repeat(64));
        let signed_v2 = signer.sign_receipt(&v2).await.unwrap();
        assert!(ReceiptValidator::validate_receipt(&signed_v2).await.unwrap());
        assert!(signer.verify_receipt(&signed_v2).unwrap());

        for malformed in [
            format!("sha256-v2:{}", "g".repeat(64)),
            format!("sha256-v2:{}", "A".repeat(64)),
            "sha256-v3:unrecognized".to_string(),
            "g".repeat(64),
        ] {
            let mut candidate = sample_receipt();
            candidate.result_hash = malformed;
            let signed_candidate = signer.sign_receipt(&candidate).await.unwrap();
            assert!(!ReceiptValidator::validate_receipt(&signed_candidate).await.unwrap());
        }
    }
    #[tokio::test]
    async fn test_local_verifier_rejects_other_key_and_tampered_fields() {
        // Independent keys, no trust-root or opt-out environment dependency.
        let signer = ReceiptSigner {
            signing_key: SigningKey::from_bytes(&[17_u8; 32]),
            key_id: "issuer-a".into(),
        };
        let unrelated = ReceiptSigner {
            signing_key: SigningKey::from_bytes(&[19_u8; 32]),
            key_id: "issuer-b".into(),
        };
        let signed = signer.sign_receipt(&sample_receipt()).await.unwrap();
        assert!(signer.verify_receipt(&signed).unwrap());
        assert!(!unrelated.verify_receipt(&signed).unwrap());

        let mut tampered = signed.clone();
        tampered.tenant = "other-tenant".into();
        assert!(!signer.verify_receipt(&tampered).unwrap());

        tampered = signed.clone();
        tampered.result_hash = "c".repeat(64);
        assert!(!signer.verify_receipt(&tampered).unwrap());

        tampered = signed.clone();
        tampered.sig = "malformed".into();
        assert!(!signer.verify_receipt(&tampered).unwrap());

        tampered = signed;
        tampered.sign_alg = "none".into();
        assert!(!signer.verify_receipt(&tampered).unwrap());
    }

    #[tokio::test]
    async fn test_receipt_numeric_fields_preserve_canonical_representation() {
        let signer = ReceiptSigner {
            signing_key: SigningKey::from_bytes(&[31_u8; 32]),
            key_id: "numeric-boundary-fixture".into(),
        };
        let mut boundary = sample_receipt();
        boundary.result_count = i32::MAX as usize;
        boundary.query_time_ms = i32::MAX as u64;
        let signed_boundary = signer.sign_receipt(&boundary).await.unwrap();
        assert!(signer.verify_receipt(&signed_boundary).unwrap());
        assert!(signer.dsse_envelope(&boundary).is_ok());

        let signed = signer.sign_receipt(&sample_receipt()).await.unwrap();
        let mut oversized = signed.clone();
        oversized.query_time_ms = (i32::MAX as u64) + 1;
        assert!(signer.sign_receipt(&oversized).await.is_err());
        assert!(signer.dsse_envelope(&oversized).is_err());
        assert!(!signer.verify_receipt(&oversized).unwrap());
        assert!(!ReceiptValidator::validate_receipt(&oversized).await.unwrap());

        oversized = signed.clone();
        oversized.result_count = (i32::MAX as usize) + 1;
        assert!(signer.sign_receipt(&oversized).await.is_err());
        assert!(signer.dsse_envelope(&oversized).is_err());
        assert!(!signer.verify_receipt(&oversized).unwrap());
        assert!(!ReceiptValidator::validate_receipt(&oversized).await.unwrap());

        oversized = signed;
        oversized.timestamp = (i64::MAX as u64) + 1;
        assert!(signer.sign_receipt(&oversized).await.is_err());
        assert!(signer.dsse_envelope(&oversized).is_err());
        assert!(!signer.verify_receipt(&oversized).unwrap());
        assert!(!ReceiptValidator::validate_receipt(&oversized).await.unwrap());
    }

    #[tokio::test]
    async fn test_external_validator_never_accepts_disabled_dsse_mode() {
        let _env_guard = RECEIPT_TEST_ENV.lock().unwrap_or_else(|e| e.into_inner());
        let fixtures = crypto_fixtures_dir();
        set_test_signing_env(&fixtures);
        // The lower-level DSSE library deliberately supports a dev-only
        // structural bypass. This external validator must stay strict.
        std::env::set_var("PF_ENFORCE_DSSE", "0");

        let issuer = ReceiptSigner::new().await.unwrap();
        let signed = issuer.sign_receipt(&sample_receipt()).await.unwrap();
        assert!(ReceiptValidator::validate_receipt(&signed).await.unwrap());

        // The signature must bind the full unsigned numeric field values.
        let mut altered = signed.clone();
        altered.query_time_ms += 1_u64 << 32;
        assert!(!issuer.verify_receipt(&altered).unwrap());
        assert!(!ReceiptValidator::validate_receipt(&altered).await.unwrap());

        if let Ok(offset) = usize::try_from(1_u64 << 32) {
            let mut altered = signed.clone();
            altered.result_count += offset;
            assert!(!issuer.verify_receipt(&altered).unwrap());
            assert!(!ReceiptValidator::validate_receipt(&altered).await.unwrap());
        }

        let unrelated_issuer = ReceiptSigner {
            signing_key: SigningKey::from_bytes(&[29_u8; 32]),
            key_id: "unrelated".into(),
        };
        let forged = unrelated_issuer.sign_receipt(&sample_receipt()).await.unwrap();
        assert!(!ReceiptValidator::validate_receipt(&forged).await.unwrap());

        std::env::remove_var("PF_TRUST_ROOT_PEM");
        assert!(!ReceiptValidator::validate_receipt(&signed).await.unwrap());

        std::env::set_var("PF_ENFORCE_DSSE", "1");
        std::env::set_var("PF_TRUST_ROOT_PEM", fixtures.join("ed25519_public.pem"));
    }

}
