/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * you may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::error::Error;

use crate::time_util;

const EGRESS_SIGNATURE_ALGORITHM: &str = "ed25519-pf-egress-v1";
const EGRESS_SIGNATURE_DOMAIN: &[u8] = b"provability-fabric:egress-certificate:v1\0";

// Encode objects in sorted key order regardless of HashMap iteration order
// or serde_json's preserve_order feature. This is the versioned Rust wire
// format, not a claim of RFC 8785 cross-language canonicalization.
fn write_sorted_json(value: &serde_json::Value, out: &mut Vec<u8>) -> serde_json::Result<()> {
    match value {
        serde_json::Value::Object(map) => {
            let mut fields: Vec<_> = map.iter().collect();
            fields.sort_unstable_by(|a, b| a.0.cmp(b.0));
            out.push(b'{');
            for (i, (key, value)) in fields.into_iter().enumerate() {
                if i != 0 { out.push(b','); }
                serde_json::to_writer(&mut *out, key)?;
                out.push(b':');
                write_sorted_json(value, out)?;
            }
            out.push(b'}');
        }
        serde_json::Value::Array(values) => {
            out.push(b'[');
            for (i, value) in values.iter().enumerate() {
                if i != 0 { out.push(b','); }
                write_sorted_json(value, out)?;
            }
            out.push(b']');
        }
        _ => serde_json::to_writer(&mut *out, value)?,
    }
    Ok(())
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn decode_hex<const N: usize>(value: &str) -> Option<[u8; N]> {
    if value.len() != N * 2 || !value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
        return None;
    }
    let mut decoded = [0; N];
    for (i, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        decoded[i] = u8::from_str_radix(std::str::from_utf8(pair).ok()?, 16).ok()?;
    }
    Some(decoded)
}

/// Egress certificate configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertConfig {
    pub enable_certification: bool,
    pub require_signature: bool,
    pub signature_algorithm: String,
    pub certificate_ttl_seconds: u64,
    pub enable_audit_logging: bool,
    pub max_certificates_per_session: usize,
}

impl Default for EgressCertConfig {
    fn default() -> Self {
        Self {
            enable_certification: true,
            require_signature: true,
            signature_algorithm: EGRESS_SIGNATURE_ALGORITHM.to_string(),
            certificate_ttl_seconds: 3600, // 1 hour
            enable_audit_logging: true,
            max_certificates_per_session: 100,
        }
    }
}

/// Egress certificate metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertMetadata {
    pub certificate_id: String,
    pub session_id: String,
    pub bundle_id: String,
    pub plan_hash: String,
    pub created_at: u64,
    pub expires_at: u64,
    pub issuer: String,
    pub version: String,
}

/// Egress certificate content
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertContent {
    pub metadata: EgressCertMetadata,
    pub policy_hash: String,
    pub decision_log: Vec<DecisionEntry>,
    pub non_interference_verdict: NIVerdict,
    pub rate_limit_status: RateLimitStatus,
    pub declassification_log: Vec<DeclassEntry>,
    pub effects_log: Vec<EffectEntry>,
    pub witness_verification: WitnessVerification,
    pub permission_evidence: PermissionEvidence, // NEW: Permission evidence
    pub proof_hashes: ProofHashes,               // NEW: Proof hashes for verification
    pub bridge_guarantee: BridgeGuarantee, // NEW: Bridge guarantee linking to Theorem ni-bridge
}

/// NEW: Permission evidence for each operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionEvidence {
    pub permit_decision: String, // "accept", "reject", "error"
    pub path_witness_ok: bool,
    pub label_derivation_ok: bool,
    pub epoch: u64,
    pub principal_id: String,
    pub action_type: String, // "call", "read", "write", "grant"
    pub resource_id: String,
    pub field_path: Option<Vec<String>>,
    pub abac_attributes: HashMap<String, String>,
    pub session_attributes: HashMap<String, String>,
    pub scope: Option<String>,
    pub tenant: String,
    pub timestamp: u64,
}

/// NEW: Proof hashes for verification
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct ProofHashes {
    pub automata_hash: String,   // Hash of proof/Automata
    pub labeler_hash: String,    // Hash of proof/Automata/Labeler
    pub policy_hash: String,     // Hash of the policy specification
    pub ni_monitor_hash: String, // Hash of the NI monitor implementation
}

/// NEW: Bridge guarantee linking local checks to global NI claims
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeGuarantee {
    pub theorem_reference: String,      // "ni-bridge"
    pub local_checks_ok: bool,          // permitD + witness validation passed
    pub global_ni_claim: String,        // Reference to the global non-interference property
    pub proof_verification: bool,       // Proof hashes match expected values
    pub bridge_conditions: Vec<String>, // List of conditions that must hold for the bridge
}

/// Decision log entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionEntry {
    pub timestamp: u64,
    pub operation: String,
    pub decision: String,
    pub reason: String,
    pub user_id: String,
    pub session_id: String,
    pub metadata: HashMap<String, String>,
}

/// Non-interference verdict
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIVerdict {
    pub verdict: String, // "pass", "fail", "unknown"
    pub confidence: f64, // 0.0 to 1.0
    pub violations: Vec<String>,
    pub prefix_count: usize,
    pub verification_time_ms: u64,
    pub ni_monitor: String, // NEW: Reference to \MonNI implementation
}

/// Rate limit status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitStatus {
    pub overall_status: String, // "within_limits", "exceeded", "unknown"
    pub rate_limits: Vec<RateLimitInfo>,
    pub total_requests: u64,
    pub window_start: u64,
    pub window_end: u64,
}

/// Rate limit information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitInfo {
    pub limit_name: String,
    pub current_count: u64,
    pub max_count: u64,
    pub window_ms: u64,
    pub status: String, // "within_limit", "approaching", "exceeded"
}

/// Declassification entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclassEntry {
    pub timestamp: u64,
    pub from_label: String,
    pub to_label: String,
    pub condition: String,
    pub justification: String,
    pub approved_by: String,
    pub rule_id: String,
}

/// Effect entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectEntry {
    pub timestamp: u64,
    pub effect_type: String, // "read", "write", "network", "file_system", "database"
    pub resource_id: String,
    pub field_path: Option<Vec<String>>,
    pub metadata: HashMap<String, String>,
}

/// Witness verification
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct WitnessVerification {
    pub merkle_path_valid: bool,
    pub field_commit_valid: bool,
    pub label_derivation_valid: bool,
    pub witness_hash: String,
    pub verification_time_ms: u64,
}

/// Egress certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertificate {
    pub content: EgressCertContent,
    pub signature: Option<String>,
    pub signature_algorithm: String,
    pub public_key: Option<String>,
    pub certificate_chain: Vec<String>,
}

impl EgressCertificate {
    /// Create a new egress certificate
    pub fn new(
        session_id: String,
        bundle_id: String,
        plan_hash: String,
        policy_hash: String,
    ) -> Self {
        let now = time_util::unix_secs();

        let metadata = EgressCertMetadata {
            certificate_id: Self::generate_certificate_id(),
            session_id,
            bundle_id,
            plan_hash,
            created_at: now,
            expires_at: now + 3600, // 1 hour TTL
            issuer: "provability-fabric".to_string(),
            version: "v2.0".to_string(), // Updated version for new schema
        };

        let content = EgressCertContent {
            metadata,
            policy_hash,
            decision_log: Vec::new(),
            non_interference_verdict: NIVerdict::default(),
            rate_limit_status: RateLimitStatus::default(),
            declassification_log: Vec::new(),
            effects_log: Vec::new(),
            witness_verification: WitnessVerification::default(),
            permission_evidence: PermissionEvidence::default(),
            proof_hashes: ProofHashes::default(),
            bridge_guarantee: BridgeGuarantee::default(),
        };

        Self {
            content,
            signature: None,
            signature_algorithm: EGRESS_SIGNATURE_ALGORITHM.to_string(),
            public_key: None,
            certificate_chain: Vec::new(),
        }
    }

    /// Generate a unique certificate ID
    fn generate_certificate_id() -> String {
        let mut hasher = Sha256::new();
        let timestamp = time_util::unix_nanos();
        hasher.update(timestamp.to_string().as_bytes());
        format!("cert_{:x}", hasher.finalize())
    }

    /// Add a decision entry
    pub fn add_decision(&mut self, entry: DecisionEntry) {
        self.content.decision_log.push(entry);
    }

    /// Add permission evidence
    pub fn add_permission_evidence(&mut self, evidence: PermissionEvidence) {
        self.content.permission_evidence = evidence;
    }

    /// Add proof hashes
    pub fn add_proof_hashes(&mut self, hashes: ProofHashes) {
        self.content.proof_hashes = hashes;
    }

    /// Update non-interference verdict
    pub fn update_ni_verdict(&mut self, verdict: NIVerdict) {
        self.content.non_interference_verdict = verdict;
    }

    /// Update witness verification
    pub fn update_witness_verification(&mut self, verification: WitnessVerification) {
        self.content.witness_verification = verification;
    }

    /// Versioned, domain-separated signature input for this content type.
    fn signature_input(&self) -> Result<Vec<u8>, Box<dyn Error>> {
        let confidence = self.content.non_interference_verdict.confidence;
        if !confidence.is_finite() || !(0.0..=1.0).contains(&confidence) {
            return Err("invalid non-interference confidence".into());
        }
        let mut bytes = EGRESS_SIGNATURE_DOMAIN.to_vec();
        write_sorted_json(&serde_json::to_value(&self.content)?, &mut bytes)?;
        Ok(bytes)
    }

    /// Sign with an actual Ed25519 private key. This authenticates the
    /// content; it does not establish that its policy claims are true.
    pub fn sign(&mut self, signing_key: &SigningKey) -> Result<(), Box<dyn Error>> {
        let signature = signing_key.sign(&self.signature_input()?);
        self.signature_algorithm = EGRESS_SIGNATURE_ALGORITHM.to_string();
        self.signature = Some(encode_hex(&signature.to_bytes()));
        self.public_key = Some(encode_hex(signing_key.verifying_key().as_bytes()));
        // This format does not implement certificate-chain verification.
        self.certificate_chain.clear();
        Ok(())
    }

    /// Authenticate against an independently provisioned verification key.
    /// The embedded key is an identity hint, never a source of trust.
    /// Legacy unkeyed digests and unsupported chain formats are rejected.
    pub fn verify_signature(&self, trusted_key: &VerifyingKey) -> Result<bool, Box<dyn Error>> {
        if self.signature_algorithm != EGRESS_SIGNATURE_ALGORITHM
            || !self.certificate_chain.is_empty()
            || self.public_key.as_deref() != Some(encode_hex(trusted_key.as_bytes()).as_str())
        {
            return Ok(false);
        }
        let Some(bytes) = self.signature.as_deref().and_then(decode_hex::<64>) else {
            return Ok(false);
        };
        let signature = Signature::from_bytes(&bytes);
        Ok(trusted_key.verify_strict(&self.signature_input()?, &signature).is_ok())
    }

    /// Get certificate hash for transparency log
    pub fn get_certificate_hash(&self) -> String {
        let mut hasher = Sha256::new();
        let content_json = serde_json::to_string(&self.content).unwrap_or_default();
        hasher.update(content_json.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Check if certificate is expired
    pub fn is_expired(&self) -> bool {
        let now = time_util::unix_secs();
        now > self.content.metadata.expires_at
    }

    /// Get certificate summary for logging
    pub fn get_summary(&self) -> String {
        format!(
            "Certificate {} for session {} ({} decisions, NI: {}, Permit: {})",
            self.content.metadata.certificate_id,
            self.content.metadata.session_id,
            self.content.decision_log.len(),
            self.content.non_interference_verdict.verdict,
            self.content.permission_evidence.permit_decision
        )
    }
}

impl Default for NIVerdict {
    fn default() -> Self {
        Self {
            verdict: "unknown".to_string(),
            confidence: 0.0,
            violations: Vec::new(),
            prefix_count: 0,
            verification_time_ms: 0,
            ni_monitor: "\\MonNI_L".to_string(), // Reference to \MonNI definition
        }
    }
}

impl Default for RateLimitStatus {
    fn default() -> Self {
        let now = time_util::unix_secs();

        Self {
            overall_status: "within_limits".to_string(),
            rate_limits: Vec::new(),
            total_requests: 0,
            window_start: now,
            window_end: now + 3600,
        }
    }
}


impl Default for PermissionEvidence {
    fn default() -> Self {
        Self {
            permit_decision: "error".to_string(),
            path_witness_ok: false,
            label_derivation_ok: false,
            epoch: 0,
            principal_id: String::new(),
            action_type: String::new(),
            resource_id: String::new(),
            field_path: None,
            abac_attributes: HashMap::new(),
            session_attributes: HashMap::new(),
            scope: None,
            tenant: String::new(),
            timestamp: 0,
        }
    }
}


impl Default for BridgeGuarantee {
    fn default() -> Self {
        Self {
            theorem_reference: "ni-bridge".to_string(),
            local_checks_ok: false,
            global_ni_claim: String::new(),
            proof_verification: false,
            bridge_conditions: Vec::new(),
        }
    }
}

/// Bridge guarantee documentation
///
/// This certificate provides evidence that the runtime's local non-interference checks
/// align with the global non-interference claims proven in the Lean specification.
///
/// Bridge Guarantee: If permitD accepts and \MonNI accepts for all prefixes, then
/// low views coincide. This is proven in Theorem~ni-bridge in the Lean specification.
///
/// The runtime ensures this by:
/// 1. Calling permitD for every event (call/read/write/declassify/emit)
/// 2. Setting ni_monitor exactly as \MonNI_L definition requires
/// 3. Including proof hashes for verification
/// 4. Emitting structured permission evidence
///
/// See proofs/Policy.lean for the formal specification and proofs.

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_certificate_creation() {
        let cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        assert_eq!(cert.content.metadata.session_id, "session-1");
        assert_eq!(cert.content.metadata.bundle_id, "bundle-1");
        assert_eq!(cert.content.metadata.plan_hash, "plan-hash-123");
        assert_eq!(cert.content.policy_hash, "policy-hash-456");
        assert_eq!(cert.content.metadata.version, "v2.0");
    }

    #[test]
    fn test_permission_evidence() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        let evidence = PermissionEvidence {
            permit_decision: "accept".to_string(),
            path_witness_ok: true,
            label_derivation_ok: true,
            epoch: 1,
            principal_id: "user-1".to_string(),
            action_type: "read".to_string(),
            resource_id: "doc://test".to_string(),
            field_path: Some(vec!["field1".to_string()]),
            abac_attributes: HashMap::new(),
            session_attributes: HashMap::new(),
            scope: Some("tenant-a".to_string()),
            tenant: "tenant-a".to_string(),
            timestamp: 1,
        };

        cert.add_permission_evidence(evidence);
        assert_eq!(cert.content.permission_evidence.permit_decision, "accept");
        assert_eq!(cert.content.permission_evidence.principal_id, "user-1");
    }

    #[test]
    fn test_proof_hashes() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        let hashes = ProofHashes {
            automata_hash: "hash123".to_string(),
            labeler_hash: "hash456".to_string(),
            policy_hash: "hash789".to_string(),
            ni_monitor_hash: "hash012".to_string(),
        };

        cert.add_proof_hashes(hashes);
        assert_eq!(cert.content.proof_hashes.automata_hash, "hash123");
        assert_eq!(cert.content.proof_hashes.labeler_hash, "hash456");
    }

    #[test]
    fn test_certificate_signing() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        let key = SigningKey::from_bytes(&[7; 32]);
        let unrelated = SigningKey::from_bytes(&[8; 32]);
        assert!(!cert.verify_signature(&key.verifying_key()).unwrap());
        cert.sign(&key).unwrap();
        assert!(cert.signature.is_some());
        assert!(cert.verify_signature(&key.verifying_key()).unwrap());
        assert!(!cert.verify_signature(&unrelated.verifying_key()).unwrap());

        let mut tampered = cert.clone();
        tampered.content.permission_evidence.permit_decision = "accept".into();
        assert!(!tampered.verify_signature(&key.verifying_key()).unwrap());

        let mut forged = cert.clone();
        forged.sign(&unrelated).unwrap();
        assert!(!forged.verify_signature(&key.verifying_key()).unwrap());

        let mut legacy = cert.clone();
        legacy.signature_algorithm = "sha256".into();
        legacy.signature = Some(format!("sig_{}", legacy.get_certificate_hash()));
        assert!(!legacy.verify_signature(&key.verifying_key()).unwrap());

        let mut malformed = cert.clone();
        malformed.signature = Some("zz".repeat(64));
        assert!(!malformed.verify_signature(&key.verifying_key()).unwrap());
        let mut untrusted_chain = cert.clone();
        untrusted_chain.certificate_chain.push("unverified".into());
        assert!(!untrusted_chain.verify_signature(&key.verifying_key()).unwrap());
    }

    #[test]
    fn test_certificate_expiry() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        // Set expiry to past
        cert.content.metadata.expires_at = 0;
        assert!(cert.is_expired());

        // Set expiry to future
        let future = crate::time_util::unix_secs() + 3600;
        cert.content.metadata.expires_at = future;
        assert!(!cert.is_expired());
    }

    #[test]
    fn test_egress_certificate_validation() {
        let cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );
        assert!(!cert.content.metadata.session_id.is_empty());
    }

    #[test]
    fn test_egress_certificate_schema_validation() {
        let cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );
        assert_eq!(cert.content.metadata.version, "v2.0");
    }

    #[test]
    fn test_egress_certificate_ed25519_signature() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );
        let key = SigningKey::from_bytes(&[9; 32]);
        cert.content.permission_evidence.abac_attributes =
            HashMap::from([("a".into(), "1".into()), ("b".into(), "2".into())]);
        cert.sign(&key).unwrap();
        let encoded = serde_json::to_string(&cert).unwrap();
        let mut imported: EgressCertificate = serde_json::from_str(&encoded).unwrap();
        assert!(imported.verify_signature(&key.verifying_key()).unwrap());
        imported.content.permission_evidence.abac_attributes =
            HashMap::from([("b".into(), "2".into()), ("a".into(), "1".into())]);
        assert!(imported.verify_signature(&key.verifying_key()).unwrap());
        imported.content.permission_evidence.abac_attributes.insert("a".into(), "3".into());
        assert!(!imported.verify_signature(&key.verifying_key()).unwrap());
    }

    #[test]
    fn test_egress_certificate_export_import() {
        let cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );
        let exported = serde_json::to_string(&cert).unwrap();
        let imported: EgressCertificate = serde_json::from_str(&exported).unwrap();
        assert_eq!(imported.content.metadata.session_id, "session-1");
    }

    #[test]
    fn test_egress_certificate_expiry_handling() {
        let mut cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );
        cert.content.metadata.expires_at = 0;
        assert!(cert.is_expired());
    }
}
