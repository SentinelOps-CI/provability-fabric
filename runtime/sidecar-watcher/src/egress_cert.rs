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
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::error::Error;
use std::time::{SystemTime, UNIX_EPOCH};

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
            signature_algorithm: "sha256".to_string(),
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
    pub operation: String,
    pub current_count: u64,
    pub limit: u64,
    pub window_ms: u64,
    pub status: String, // "within_limit", "exceeded"
}

/// Declassification entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclassEntry {
    pub timestamp: u64,
    pub from_label: String,
    pub to_label: String,
    pub justification: String,
    pub user_id: String,
    pub approved_by: Option<String>,
    pub conditions: Vec<String>,
}

/// Effect entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EffectEntry {
    pub timestamp: u64,
    pub effect_type: String,
    pub resource: String,
    pub allowed: bool,
    pub constraints: HashMap<String, String>,
    pub user_id: String,
}

/// Witness verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessVerification {
    pub merkle_root: String,
    pub bloom_filter: String,
    pub verified_paths: Vec<String>,
    pub verification_time_ms: u64,
    pub verification_status: String, // "verified", "failed", "partial"
}

/// Egress certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertificate {
    pub content: EgressCertContent,
    pub signature: Option<String>,
    pub signature_algorithm: String,
    pub public_key: Option<String>,
    pub certificate_hash: String,
}

impl EgressCertificate {
    /// Create new egress certificate
    pub fn new(
        session_id: String,
        bundle_id: String,
        plan_hash: String,
        issuer: String,
        config: &EgressCertConfig,
    ) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let expires_at = now + config.certificate_ttl_seconds;

        let metadata = EgressCertMetadata {
            certificate_id: format!("egress_cert_{}_{}", session_id, now),
            session_id,
            bundle_id,
            plan_hash,
            created_at: now,
            expires_at,
            issuer,
            version: "v1".to_string(),
        };

        let content = EgressCertContent {
            metadata,
            policy_hash: String::new(),
            decision_log: Vec::new(),
            non_interference_verdict: NIVerdict {
                verdict: "unknown".to_string(),
                confidence: 0.0,
                violations: Vec::new(),
                prefix_count: 0,
                verification_time_ms: 0,
            },
            rate_limit_status: RateLimitStatus {
                overall_status: "unknown".to_string(),
                rate_limits: Vec::new(),
                total_requests: 0,
                window_start: now,
                window_end: now + 3600,
            },
            declassification_log: Vec::new(),
            effects_log: Vec::new(),
            witness_verification: WitnessVerification {
                merkle_root: String::new(),
                bloom_filter: String::new(),
                verified_paths: Vec::new(),
                verification_time_ms: 0,
                verification_status: "unknown".to_string(),
            },
        };

        let certificate_hash = Self::compute_certificate_hash(&content);

        Self {
            content,
            signature: None,
            signature_algorithm: config.signature_algorithm.clone(),
            public_key: None,
            certificate_hash,
        }
    }

    /// Compute certificate hash
    fn compute_certificate_hash(content: &EgressCertContent) -> String {
        let mut hasher = Sha256::new();

        // Hash metadata
        hasher.update(content.metadata.certificate_id.as_bytes());
        hasher.update(content.metadata.session_id.as_bytes());
        hasher.update(content.metadata.bundle_id.as_bytes());
        hasher.update(content.metadata.plan_hash.as_bytes());
        hasher.update(content.metadata.created_at.to_string().as_bytes());

        // Hash policy hash
        hasher.update(content.policy_hash.as_bytes());

        // Hash decision log
        for entry in &content.decision_log {
            hasher.update(entry.timestamp.to_string().as_bytes());
            hasher.update(entry.operation.as_bytes());
            hasher.update(entry.decision.as_bytes());
        }

        // Hash NI verdict
        hasher.update(content.non_interference_verdict.verdict.as_bytes());
        hasher.update(
            content
                .non_interference_verdict
                .confidence
                .to_string()
                .as_bytes(),
        );

        format!("{:x}", hasher.finalize())
    }

    /// Add decision log entry
    pub fn add_decision(&mut self, entry: DecisionEntry) {
        self.content.decision_log.push(entry);
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Update non-interference verdict
    pub fn update_ni_verdict(&mut self, verdict: NIVerdict) {
        self.content.non_interference_verdict = verdict;
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Update rate limit status
    pub fn update_rate_limit_status(&mut self, status: RateLimitStatus) {
        self.content.rate_limit_status = status;
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Add declassification entry
    pub fn add_declassification(&mut self, entry: DeclassEntry) {
        self.content.declassification_log.push(entry);
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Add effect entry
    pub fn add_effect(&mut self, entry: EffectEntry) {
        self.content.effects_log.push(entry);
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Update witness verification
    pub fn update_witness_verification(&mut self, verification: WitnessVerification) {
        self.content.witness_verification = verification;
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Set policy hash
    pub fn set_policy_hash(&mut self, policy_hash: String) {
        self.content.policy_hash = policy_hash;
        // Recompute hash
        self.certificate_hash = Self::compute_certificate_hash(&self.content);
    }

    /// Sign certificate
    pub fn sign(&mut self, private_key: &str) -> Result<(), String> {
        // In a real implementation, this would use proper cryptographic signing
        // For now, we'll create a simple hash-based signature
        let mut hasher = Sha256::new();
        hasher.update(self.certificate_hash.as_bytes());
        hasher.update(private_key.as_bytes());

        self.signature = Some(format!("{:x}", hasher.finalize()));
        Ok(())
    }

    /// Verify certificate signature
    pub fn verify_signature(&self, public_key: &str) -> Result<bool, String> {
        if let Some(signature) = &self.signature {
            // In a real implementation, this would verify the cryptographic signature
            // For now, we'll do a simple hash verification
            let mut hasher = Sha256::new();
            hasher.update(self.certificate_hash.as_bytes());
            hasher.update(public_key.as_bytes());

            let expected_signature = format!("{:x}", hasher.finalize());
            Ok(signature == &expected_signature)
        } else {
            Err("Certificate is not signed".to_string())
        }
    }

    /// Check if certificate is expired
    pub fn is_expired(&self) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        now > self.content.metadata.expires_at
    }

    /// Get certificate as JSON
    pub fn to_json(&self) -> Result<String, Box<dyn Error>> {
        Ok(serde_json::to_string_pretty(self)?)
    }

    /// Export certificate to file
    pub fn export_to_file<P: AsRef<std::path::Path>>(&self, path: P) -> Result<(), Box<dyn Error>> {
        let json_content = self.to_json()?;
        std::fs::write(path, json_content)?;
        Ok(())
    }
}

/// Egress certificate manager
pub struct EgressCertManager {
    config: EgressCertConfig,
    certificates: HashMap<String, EgressCertificate>,
    session_certificates: HashMap<String, Vec<String>>,
}

impl EgressCertManager {
    /// Create new egress certificate manager
    pub fn new(config: EgressCertConfig) -> Self {
        Self {
            config,
            certificates: HashMap::new(),
            session_certificates: HashMap::new(),
        }
    }

    /// Create new certificate for session
    pub fn create_certificate(
        &mut self,
        session_id: String,
        bundle_id: String,
        plan_hash: String,
        issuer: String,
    ) -> Result<String, String> {
        if !self.config.enable_certification {
            return Err("Certificate generation is disabled".to_string());
        }

        // Check session certificate limit
        if let Some(certs) = self.session_certificates.get(&session_id) {
            if certs.len() >= self.config.max_certificates_per_session {
                return Err("Maximum certificates per session exceeded".to_string());
            }
        }

        let certificate = EgressCertificate::new(
            session_id.clone(),
            bundle_id,
            plan_hash,
            issuer,
            &self.config,
        );

        let cert_id = certificate.content.metadata.certificate_id.clone();

        // Store certificate
        self.certificates.insert(cert_id.clone(), certificate);

        // Track session certificates
        self.session_certificates
            .entry(session_id)
            .or_insert_with(Vec::new)
            .push(cert_id.clone());

        Ok(cert_id)
    }

    /// Get certificate by ID
    pub fn get_certificate(&self, cert_id: &str) -> Option<&EgressCertificate> {
        self.certificates.get(cert_id)
    }

    /// Get certificates for session
    pub fn get_session_certificates(&self, session_id: &str) -> Vec<&EgressCertificate> {
        if let Some(cert_ids) = self.session_certificates.get(session_id) {
            cert_ids
                .iter()
                .filter_map(|id| self.certificates.get(id))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Update certificate
    pub fn update_certificate(
        &mut self,
        cert_id: &str,
        updates: CertificateUpdates,
    ) -> Result<(), String> {
        let certificate = self
            .certificates
            .get_mut(cert_id)
            .ok_or_else(|| format!("Certificate {} not found", cert_id))?;

        // Apply updates
        if let Some(decision) = updates.decision {
            certificate.add_decision(decision);
        }

        if let Some(ni_verdict) = updates.ni_verdict {
            certificate.update_ni_verdict(ni_verdict);
        }

        if let Some(rate_limit_status) = updates.rate_limit_status {
            certificate.update_rate_limit_status(rate_limit_status);
        }

        if let Some(declass_entry) = updates.declass_entry {
            certificate.add_declassification(declass_entry);
        }

        if let Some(effect_entry) = updates.effect_entry {
            certificate.add_effect(effect_entry);
        }

        if let Some(witness_verification) = updates.witness_verification {
            certificate.update_witness_verification(witness_verification);
        }

        if let Some(policy_hash) = updates.policy_hash {
            certificate.set_policy_hash(policy_hash);
        }

        Ok(())
    }

    /// Sign certificate
    pub fn sign_certificate(&mut self, cert_id: &str, private_key: &str) -> Result<(), String> {
        let certificate = self
            .certificates
            .get_mut(cert_id)
            .ok_or_else(|| format!("Certificate {} not found", cert_id))?;

        certificate.sign(private_key)
    }

    /// Verify certificate
    pub fn verify_certificate(&self, cert_id: &str, public_key: &str) -> Result<bool, String> {
        let certificate = self
            .certificates
            .get(cert_id)
            .ok_or_else(|| format!("Certificate {} not found", cert_id))?;

        certificate.verify_signature(public_key)
    }

    /// Export certificate to file
    pub fn export_certificate<P: AsRef<std::path::Path>>(
        &self,
        cert_id: &str,
        path: P,
    ) -> Result<(), Box<dyn Error>> {
        let certificate = self
            .certificates
            .get(cert_id)
            .ok_or_else(|| format!("Certificate {} not found", cert_id))?;

        certificate.export_to_file(path)
    }

    /// Clean up expired certificates
    pub fn cleanup_expired(&mut self) -> usize {
        let mut expired_certs = Vec::new();

        for (cert_id, cert) in &self.certificates {
            if cert.is_expired() {
                expired_certs.push(cert_id.clone());
            }
        }

        let expired_count = expired_certs.len();

        for cert_id in expired_certs {
            self.certificates.remove(&cert_id);
        }

        // Clean up session references
        for cert_ids in self.session_certificates.values_mut() {
            cert_ids.retain(|id| self.certificates.contains_key(id));
        }

        expired_count
    }

    /// Get manager statistics
    pub fn get_stats(&self) -> CertManagerStats {
        let total_certificates = self.certificates.len();
        let total_sessions = self.session_certificates.len();
        let expired_certificates = self
            .certificates
            .values()
            .filter(|cert| cert.is_expired())
            .count();

        CertManagerStats {
            total_certificates,
            total_sessions,
            expired_certificates,
            config: self.config.clone(),
        }
    }
}

/// Certificate updates
#[derive(Debug, Clone)]
pub struct CertificateUpdates {
    pub decision: Option<DecisionEntry>,
    pub ni_verdict: Option<NIVerdict>,
    pub rate_limit_status: Option<RateLimitStatus>,
    pub declass_entry: Option<DeclassEntry>,
    pub effect_entry: Option<EffectEntry>,
    pub witness_verification: Option<WitnessVerification>,
    pub policy_hash: Option<String>,
}

/// Certificate manager statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertManagerStats {
    pub total_certificates: usize,
    pub total_sessions: usize,
    pub expired_certificates: usize,
    pub config: EgressCertConfig,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_certificate_creation() {
        let config = EgressCertConfig::default();
        let mut manager = EgressCertManager::new(config);

        let cert_id = manager
            .create_certificate(
                "session1".to_string(),
                "bundle1".to_string(),
                "plan_hash_123".to_string(),
                "issuer1".to_string(),
            )
            .unwrap();

        assert!(!cert_id.is_empty());
        assert_eq!(manager.get_stats().total_certificates, 1);
    }

    #[test]
    fn test_certificate_updates() {
        let config = EgressCertConfig::default();
        let mut manager = EgressCertManager::new(config);

        let cert_id = manager
            .create_certificate(
                "session1".to_string(),
                "bundle1".to_string(),
                "plan_hash_123".to_string(),
                "issuer1".to_string(),
            )
            .unwrap();

        let decision = DecisionEntry {
            timestamp: 1000,
            operation: "read".to_string(),
            decision: "allow".to_string(),
            reason: "authorized".to_string(),
            user_id: "user1".to_string(),
            session_id: "session1".to_string(),
            metadata: HashMap::new(),
        };

        let updates = CertificateUpdates {
            decision: Some(decision),
            ni_verdict: None,
            rate_limit_status: None,
            declass_entry: None,
            effect_entry: None,
            witness_verification: None,
            policy_hash: None,
        };

        manager.update_certificate(&cert_id, updates).unwrap();

        let cert = manager.get_certificate(&cert_id).unwrap();
        assert_eq!(cert.content.decision_log.len(), 1);
    }

    #[test]
    fn test_certificate_signing() {
        let config = EgressCertConfig::default();
        let mut manager = EgressCertManager::new(config);

        let cert_id = manager
            .create_certificate(
                "session1".to_string(),
                "bundle1".to_string(),
                "plan_hash_123".to_string(),
                "issuer1".to_string(),
            )
            .unwrap();

        manager
            .sign_certificate(&cert_id, "private_key_123")
            .unwrap();

        let cert = manager.get_certificate(&cert_id).unwrap();
        assert!(cert.signature.is_some());
        assert!(cert.verify_signature("private_key_123").unwrap());
    }

    #[test]
    fn test_certificate_expiration() {
        let mut config = EgressCertConfig::default();
        config.certificate_ttl_seconds = 1; // Very short TTL for testing
        let mut manager = EgressCertManager::new(config);

        let cert_id = manager
            .create_certificate(
                "session1".to_string(),
                "bundle1".to_string(),
                "plan_hash_123".to_string(),
                "issuer1".to_string(),
            )
            .unwrap();

        // Wait for expiration
        std::thread::sleep(std::time::Duration::from_millis(1100));

        let expired_count = manager.cleanup_expired();
        assert_eq!(expired_count, 1);
        assert_eq!(manager.get_stats().total_certificates, 0);
    }

    #[test]
    fn test_session_certificate_limit() {
        let mut config = EgressCertConfig::default();
        config.max_certificates_per_session = 2;
        let mut manager = EgressCertManager::new(config);

        // Create first two certificates
        for i in 0..2 {
            manager
                .create_certificate(
                    format!("session1"),
                    format!("bundle{}", i),
                    format!("plan_hash_{}", i),
                    "issuer1".to_string(),
                )
                .unwrap();
        }

        // Third certificate should fail
        let result = manager.create_certificate(
            "session1".to_string(),
            "bundle3".to_string(),
            "plan_hash_3".to_string(),
            "issuer1".to_string(),
        );

        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("Maximum certificates per session exceeded"));
    }
}
