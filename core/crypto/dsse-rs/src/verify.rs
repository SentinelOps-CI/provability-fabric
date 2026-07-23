// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use base64::{engine::general_purpose::STANDARD as B64_STD, Engine as _};
use ed25519_dalek::{Signature, Verifier, VerifyingKey};
use ed25519_dalek::pkcs8::DecodePublicKey;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::path::Path;
use thiserror::Error;

pub const ENV_TRUST_ROOT_PEM: &str = "PF_TRUST_ROOT_PEM";
pub const ENV_JWKS_URL: &str = "PF_JWKS_URL";
pub const ENV_ENFORCE_DSSE: &str = "PF_ENFORCE_DSSE";
pub const ACCESS_RECEIPT_TYPE: &str = "application/vnd.provability-fabric.access-receipt";

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Envelope {
    #[serde(rename = "payloadType")]
    pub payload_type: String,
    pub payload: String,
    pub signatures: Vec<EnvelopeSignature>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvelopeSignature {
    pub keyid: String,
    pub sig: String,
    #[serde(default)]
    pub alg: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct VerifyResult {
    pub valid: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccessReceiptPayload {
    pub receipt_id: String,
    pub tenant: String,
    pub subject_id: String,
    pub query_hash: String,
    pub index_shard: String,
    pub timestamp: i64,
    pub result_hash: String,
    #[serde(default)]
    pub result_count: i32,
    #[serde(default)]
    pub query_time_ms: i32,
    #[serde(default)]
    pub signature: String,
}

#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("{0}")]
    Message(String),
}

/// Returns true when DSSE verification must fail closed.
/// Default is enforce (unset). Opt out only with `PF_ENFORCE_DSSE=0` or `false`.
pub fn enforce_dsse() -> bool {
    match env::var(ENV_ENFORCE_DSSE) {
        Ok(v) => {
            let v = v.trim();
            !(v == "0" || v.eq_ignore_ascii_case("false"))
        }
        Err(_) => true,
    }
}

pub fn trust_root_configured() -> bool {
    load_trust_root_pem().is_ok()
}

fn load_trust_root_pem() -> Result<Vec<u8>, VerifyError> {
    let raw = env::var(ENV_TRUST_ROOT_PEM)
        .map_err(|_| VerifyError::Message(format!("{ENV_TRUST_ROOT_PEM} unset")))?;
    let raw = raw.trim();
    if raw.is_empty() {
        return Err(VerifyError::Message("trust root empty".into()));
    }
    if Path::new(raw).exists() {
        fs::read(raw).map_err(|e| VerifyError::Message(format!("read trust root: {e}")))
    } else {
        Ok(raw.as_bytes().to_vec())
    }
}

fn decode_sig(sig_b64: &str) -> Result<Signature, VerifyError> {
    let bytes = B64_STD
        .decode(sig_b64)
        .or_else(|_| base64::engine::general_purpose::URL_SAFE_NO_PAD.decode(sig_b64))
        .map_err(|_| VerifyError::Message("sig_decode_error".into()))?;
    let arr: [u8; 64] = bytes
        .try_into()
        .map_err(|_| VerifyError::Message("invalid signature length".into()))?;
    Ok(Signature::from_bytes(&arr))
}

pub fn load_ed25519_public_key_from_pem(pem_data: &[u8]) -> Result<VerifyingKey, VerifyError> {
    let pem_str = std::str::from_utf8(pem_data)
        .map_err(|e| VerifyError::Message(format!("invalid pem utf8: {e}")))?;
    let pem_block = pem::parse(pem_str).map_err(|e| VerifyError::Message(format!("pem parse: {e}")))?;
    DecodePublicKey::from_public_key_der(pem_block.contents())
        .map_err(|e| VerifyError::Message(format!("load public key: {e}")))
}

fn verify_signature(message: &[u8], sig_b64: &str, pem_pub: &[u8]) -> Result<(), VerifyError> {
    let sig = decode_sig(sig_b64)?;
    let key = load_ed25519_public_key_from_pem(pem_pub)?;
    key.verify(message, &sig)
        .map_err(|_| VerifyError::Message("signature_mismatch".into()))
}

pub fn verify_envelope(envelope: &Envelope, expected_payload_type: &str) -> VerifyResult {
    if !expected_payload_type.is_empty() && envelope.payload_type != expected_payload_type {
        return VerifyResult {
            valid: false,
            reason: Some("payload_type_mismatch".into()),
        };
    }
    if envelope.signatures.is_empty() {
        return VerifyResult {
            valid: false,
            reason: Some("no_signatures".into()),
        };
    }
    let payload = match B64_STD.decode(&envelope.payload) {
        Ok(p) => p,
        Err(_) => {
            return VerifyResult {
                valid: false,
                reason: Some("payload_decode_error".into()),
            }
        }
    };
    let pem_pub = match load_trust_root_pem() {
        Ok(p) => p,
        Err(e) => {
            return VerifyResult {
                valid: false,
                reason: Some(e.to_string()),
            }
        }
    };
    for sig in &envelope.signatures {
        if !sig.alg.is_empty() && !sig.alg.eq_ignore_ascii_case("ed25519") {
            continue;
        }
        if verify_signature(&payload, &sig.sig, &pem_pub).is_ok() {
            return VerifyResult {
                valid: true,
                reason: None,
            };
        }
    }
    VerifyResult {
        valid: false,
        reason: Some("signature_mismatch".into()),
    }
}

pub fn canonical_receipt_payload(receipt: &AccessReceiptPayload) -> Result<Vec<u8>, VerifyError> {
    let mut m: BTreeMap<&str, serde_json::Value> = BTreeMap::new();
    m.insert("index_shard", serde_json::json!(receipt.index_shard));
    m.insert("query_hash", serde_json::json!(receipt.query_hash));
    m.insert("receipt_id", serde_json::json!(receipt.receipt_id));
    m.insert("result_hash", serde_json::json!(receipt.result_hash));
    m.insert("signature", serde_json::json!(receipt.signature));
    m.insert("subject_id", serde_json::json!(receipt.subject_id));
    m.insert("tenant", serde_json::json!(receipt.tenant));
    m.insert("timestamp", serde_json::json!(receipt.timestamp));
    if receipt.result_count != 0 {
        m.insert("result_count", serde_json::json!(receipt.result_count));
    }
    if receipt.query_time_ms != 0 {
        m.insert("query_time_ms", serde_json::json!(receipt.query_time_ms));
    }
    serde_json::to_vec(&m).map_err(|e| VerifyError::Message(e.to_string()))
}

pub fn verify_access_receipt(
    receipt: &AccessReceiptPayload,
    sign_alg: &str,
    sig: &str,
) -> Result<(), VerifyError> {
    if receipt.receipt_id.is_empty() {
        return Err(VerifyError::Message("receipt ID is required".into()));
    }
    if receipt.tenant.is_empty() {
        return Err(VerifyError::Message("receipt tenant is required".into()));
    }
    if receipt.index_shard.is_empty() {
        return Err(VerifyError::Message("receipt index shard is required".into()));
    }
    if sign_alg != "ed25519" {
        return Err(VerifyError::Message(format!(
            "unsupported signature algorithm: {sign_alg}"
        )));
    }
    if sig.is_empty() {
        return Err(VerifyError::Message("receipt signature is required".into()));
    }
    if !enforce_dsse() {
        return Ok(());
    }
    if !trust_root_configured() {
        return Err(VerifyError::Message("trust root not configured".into()));
    }
    let payload = canonical_receipt_payload(receipt)?;
    let pem_pub = load_trust_root_pem()?;
    verify_signature(&payload, sig, &pem_pub)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use std::sync::Mutex;

    // Env-var based DSSE tests must not run concurrently.
    static ENV_LOCK: Mutex<()> = Mutex::new(());

    fn fixtures_dir() -> PathBuf {
        let candidates = [
            PathBuf::from("tests/fixtures/crypto"),
            PathBuf::from("../../tests/fixtures/crypto"),
            PathBuf::from("../../../tests/fixtures/crypto"),
        ];
        for c in candidates {
            if c.join("ed25519_public.pem").exists() {
                return c;
            }
        }
        panic!("fixtures not found");
    }

    #[test]
    fn verify_fixture_envelope() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let dir = fixtures_dir();
        std::env::set_var(ENV_TRUST_ROOT_PEM, dir.join("ed25519_public.pem"));
        std::env::set_var(ENV_ENFORCE_DSSE, "1");
        let env_data = fs::read_to_string(dir.join("dsse_sample_envelope.json")).unwrap();
        let env: Envelope = serde_json::from_str(&env_data).unwrap();
        let result = verify_envelope(&env, ACCESS_RECEIPT_TYPE);
        assert!(result.valid, "{:?}", result.reason);
    }

    #[test]
    fn enforce_dsse_default_and_opt_out() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        std::env::remove_var(ENV_ENFORCE_DSSE);
        assert!(enforce_dsse(), "unset must enforce");

        std::env::set_var(ENV_ENFORCE_DSSE, "1");
        assert!(enforce_dsse());
        std::env::set_var(ENV_ENFORCE_DSSE, "true");
        assert!(enforce_dsse());

        std::env::set_var(ENV_ENFORCE_DSSE, "0");
        assert!(!enforce_dsse());
        std::env::set_var(ENV_ENFORCE_DSSE, "false");
        assert!(!enforce_dsse());

        std::env::remove_var(ENV_ENFORCE_DSSE);
    }

    #[test]
    fn reject_receipt_without_trust_root_when_unset() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        std::env::remove_var(ENV_ENFORCE_DSSE);
        std::env::remove_var(ENV_TRUST_ROOT_PEM);
        let receipt = AccessReceiptPayload {
            receipt_id: "rcpt-1".into(),
            tenant: "tenant-a".into(),
            subject_id: "user-1".into(),
            query_hash: "abc".into(),
            index_shard: "shard-0".into(),
            timestamp: 1,
            result_hash: "deadbeef".into(),
            result_count: 0,
            query_time_ms: 0,
            signature: String::new(),
        };
        let err = verify_access_receipt(&receipt, "ed25519", "deadbeef").unwrap_err();
        assert!(
            err.to_string().contains("trust root"),
            "unexpected: {err}"
        );
    }

    #[test]
    fn structural_pass_when_opt_out() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        std::env::set_var(ENV_ENFORCE_DSSE, "0");
        std::env::remove_var(ENV_TRUST_ROOT_PEM);
        let receipt = AccessReceiptPayload {
            receipt_id: "rcpt-1".into(),
            tenant: "tenant-a".into(),
            subject_id: "user-1".into(),
            query_hash: "abc".into(),
            index_shard: "shard-0".into(),
            timestamp: 1,
            result_hash: "deadbeef".into(),
            result_count: 0,
            query_time_ms: 0,
            signature: String::new(),
        };
        verify_access_receipt(&receipt, "ed25519", "deadbeef").expect("opt-out skips crypto");
        std::env::remove_var(ENV_ENFORCE_DSSE);
    }

    #[test]
    fn reject_tampered_signature() {
        let _guard = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let dir = fixtures_dir();
        std::env::set_var(ENV_TRUST_ROOT_PEM, dir.join("ed25519_public.pem"));
        let env_data = fs::read_to_string(dir.join("dsse_sample_envelope.json")).unwrap();
        let mut env: Envelope = serde_json::from_str(&env_data).unwrap();
        env.signatures[0].sig.pop();
        env.signatures[0].sig.push('A');
        let result = verify_envelope(&env, ACCESS_RECEIPT_TYPE);
        assert!(!result.valid);
    }
}
