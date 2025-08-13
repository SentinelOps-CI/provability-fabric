// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tracing::{info, warn, error};
use sha2::{Sha256, Digest};
use base64::{Engine as _, engine::general_purpose::STANDARD as BASE64};

/// Nitro enclave attestation document structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NitroAttestationDoc {
    pub module_id: String,
    pub digest: String,
    pub timestamp: u64,
    pub validity: Validity,
    pub pcrs: HashMap<String, String>,
    pub certificate: String,
    pub cabundle: Vec<String>,
    pub signature: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Validity {
    pub not_before: u64,
    pub not_after: u64,
}

/// Expected measurements for Nitro enclaves
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NitroMeasurements {
    pub expected_pcrs: HashMap<String, String>,
    pub expected_module_id: String,
    pub expected_digest: String,
    pub max_age_seconds: u64,
}

/// Attestation verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AttestationResult {
    Valid {
        enclave_id: String,
        measurements: HashMap<String, String>,
        expires_at: u64,
    },
    Invalid {
        reason: String,
        details: String,
    },
    Expired {
        attested_at: u64,
        current_time: u64,
    },
}

/// Nitro attestation verifier
pub struct NitroVerifier {
    measurements: NitroMeasurements,
    trusted_ca_certs: Vec<Vec<u8>>,
}

impl NitroVerifier {
    pub fn new(measurements: NitroMeasurements, trusted_ca_certs: Vec<Vec<u8>>) -> Self {
        Self {
            measurements,
            trusted_ca_certs,
        }
    }

    /// Verify a Nitro attestation document
    pub async fn verify_attestation(
        &self,
        attestation_doc: &NitroAttestationDoc,
    ) -> Result<AttestationResult> {
        // 1. Verify document signature
        if !self.verify_signature(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid signature".to_string(),
                details: "Document signature verification failed".to_string(),
            });
        }

        // 2. Verify certificate chain
        if !self.verify_certificate_chain(attestation_doc).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid certificate chain".to_string(),
                details: "Certificate chain verification failed".to_string(),
            });
        }

        // 3. Verify timestamp validity
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if current_time < attestation_doc.validity.not_before {
            return Ok(AttestationResult::Invalid {
                reason: "Document not yet valid".to_string(),
                details: format!(
                    "Document valid from {}, current time {}",
                    attestation_doc.validity.not_before, current_time
                ),
            });
        }

        if current_time > attestation_doc.validity.not_after {
            return Ok(AttestationResult::Expired {
                attested_at: attestation_doc.validity.not_after,
                current_time,
            });
        }

        // 4. Verify document age
        if current_time - attestation_doc.timestamp > self.measurements.max_age_seconds {
            return Ok(AttestationResult::Expired {
                attested_at: attestation_doc.timestamp,
                current_time,
            });
        }

        // 5. Verify PCR measurements
        if !self.verify_pcr_measurements(&attestation_doc.pcrs)? {
            return Ok(AttestationResult::Invalid {
                reason: "PCR measurements mismatch".to_string(),
                details: "Platform Configuration Register values do not match expected measurements".to_string(),
            });
        }

        // 6. Verify module ID and digest
        if attestation_doc.module_id != self.measurements.expected_module_id {
            return Ok(AttestationResult::Invalid {
                reason: "Module ID mismatch".to_string(),
                details: format!(
                    "Expected {}, got {}",
                    self.measurements.expected_module_id, attestation_doc.module_id
                ),
            });
        }

        if attestation_doc.digest != self.measurements.expected_digest {
            return Ok(AttestationResult::Invalid {
                reason: "Digest mismatch".to_string(),
                details: format!(
                    "Expected {}, got {}",
                    self.measurements.expected_digest, attestation_doc.digest
                ),
            });
        }

        info!("Nitro attestation verified successfully for module {}", attestation_doc.module_id);

        Ok(AttestationResult::Valid {
            enclave_id: attestation_doc.module_id.clone(),
            measurements: attestation_doc.pcrs.clone(),
            expires_at: attestation_doc.validity.not_after,
        })
    }

    /// Verify the document signature
    async fn verify_signature(&self, doc: &NitroAttestationDoc) -> Result<bool> {
        // In production, this would verify the RSA signature using the certificate's public key
        // For now, we'll implement a basic verification
        let signature_data = format!(
            "{}{}{}{}{}",
            doc.module_id,
            doc.digest,
            doc.timestamp,
            doc.validity.not_before,
            doc.validity.not_after
        );

        let expected_signature = self.generate_expected_signature(&signature_data);
        
        Ok(doc.signature == expected_signature)
    }

    /// Verify the certificate chain
    async fn verify_certificate_chain(&self, doc: &NitroAttestationDoc) -> Result<bool> {
        // In production, this would verify the X.509 certificate chain
        // For now, we'll implement a basic verification
        if doc.certificate.is_empty() {
            return Ok(false);
        }

        // Verify the certificate is properly formatted (base64)
        if let Err(_) = BASE64.decode(&doc.certificate) {
            return Ok(false);
        }

        // Verify CA bundle is not empty
        if doc.cabundle.is_empty() {
            return Ok(false);
        }

        Ok(true)
    }

    /// Verify PCR measurements against expected values
    fn verify_pcr_measurements(&self, pcrs: &HashMap<String, String>) -> Result<bool> {
        for (pcr_index, expected_value) in &self.measurements.expected_pcrs {
            if let Some(actual_value) = pcrs.get(pcr_index) {
                if actual_value != expected_value {
                    warn!(
                        "PCR {} mismatch: expected {}, got {}",
                        pcr_index, expected_value, actual_value
                    );
                    return Ok(false);
                }
            } else {
                warn!("Required PCR {} not found in attestation", pcr_index);
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Generate expected signature for verification
    fn generate_expected_signature(&self, data: &str) -> String {
        let mut hasher = Sha256::new();
        hasher.update(data.as_bytes());
        let result = hasher.finalize();
        format!("sig_{}", BASE64.encode(result))
    }
}

/// Generate short-lived KMS token for attested enclave
pub async fn generate_kms_token(
    attestation_result: &AttestationResult,
    kms_config: &KmsConfig,
) -> Result<String> {
    match attestation_result {
        AttestationResult::Valid { enclave_id, .. } => {
            let token_data = format!(
                "enclave:{}:exp:{}:{}",
                enclave_id,
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs() + kms_config.token_ttl_seconds,
                kms_config.tenant_id
            );

            let mut hasher = Sha256::new();
            hasher.update(token_data.as_bytes());
            let hash = hasher.finalize();

            Ok(BASE64.encode(hash))
        }
        _ => Err(anyhow::anyhow!("Cannot generate token for invalid attestation")),
    }
}

/// KMS configuration for token generation
#[derive(Debug, Clone)]
pub struct KmsConfig {
    pub tenant_id: String,
    pub token_ttl_seconds: u64,
    pub max_key_operations: u32,
}

impl Default for KmsConfig {
    fn default() -> Self {
        Self {
            tenant_id: "default".to_string(),
            token_ttl_seconds: 3600, // 1 hour
            max_key_operations: 1000,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn create_test_measurements() -> NitroMeasurements {
        let mut expected_pcrs = HashMap::new();
        expected_pcrs.insert("0".to_string(), "0000000000000000000000000000000000000000000000000000000000000000".to_string());
        expected_pcrs.insert("1".to_string(), "1111111111111111111111111111111111111111111111111111111111111111".to_string());
        expected_pcrs.insert("2".to_string(), "2222222222222222222222222222222222222222222222222222222222222222".to_string());

        NitroMeasurements {
            expected_pcrs,
            expected_module_id: "test-module-123".to_string(),
            expected_digest: "test-digest-456".to_string(),
            max_age_seconds: 3600,
        }
    }

    fn create_valid_attestation_doc() -> NitroAttestationDoc {
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut pcrs = HashMap::new();
        pcrs.insert("0".to_string(), "0000000000000000000000000000000000000000000000000000000000000000".to_string());
        pcrs.insert("1".to_string(), "1111111111111111111111111111111111111111111111111111111111111111".to_string());
        pcrs.insert("2".to_string(), "2222222222222222222222222222222222222222222222222222222222222222".to_string());

        NitroAttestationDoc {
            module_id: "test-module-123".to_string(),
            digest: "test-digest-456".to_string(),
            timestamp: current_time,
            validity: Validity {
                not_before: current_time - 300, // 5 minutes ago
                not_after: current_time + 3600, // 1 hour from now
            },
            pcrs,
            certificate: "dGVzdC1jZXJ0".to_string(), // base64 encoded "test-cert"
            cabundle: vec!["dGVzdC1jYS1idW5kbGU=".to_string()], // base64 encoded "test-ca-bundle"
            signature: "".to_string(), // Will be set by verifier
        }
    }

    #[tokio::test]
    async fn test_verify_valid_attestation() {
        let measurements = create_test_measurements();
        let verifier = NitroVerifier::new(measurements, vec![]);
        let mut doc = create_valid_attestation_doc();
        
        // Generate expected signature
        let signature_data = format!(
            "{}{}{}{}{}",
            doc.module_id,
            doc.digest,
            doc.timestamp,
            doc.validity.not_before,
            doc.validity.not_after
        );
        doc.signature = verifier.generate_expected_signature(&signature_data);

        let result = verifier.verify_attestation(&doc).await.unwrap();
        
        match result {
            AttestationResult::Valid { enclave_id, .. } => {
                assert_eq!(enclave_id, "test-module-123");
            }
            _ => panic!("Expected valid attestation"),
        }
    }

    #[tokio::test]
    async fn test_verify_tampered_quote() {
        let measurements = create_test_measurements();
        let verifier = NitroVerifier::new(measurements, vec![]);
        let mut doc = create_valid_attestation_doc();
        
        // Tamper with the digest
        doc.digest = "tampered-digest".to_string();
        
        // Generate signature for tampered data
        let signature_data = format!(
            "{}{}{}{}{}",
            doc.module_id,
            doc.digest,
            doc.timestamp,
            doc.validity.not_before,
            doc.validity.not_after
        );
        doc.signature = verifier.generate_expected_signature(&signature_data);

        let result = verifier.verify_attestation(&doc).await.unwrap();
        
        match result {
            AttestationResult::Invalid { reason, .. } => {
                assert!(reason.contains("Digest mismatch"));
            }
            _ => panic!("Expected invalid attestation"),
        }
    }

    #[tokio::test]
    async fn test_generate_kms_token() {
        let measurements = create_test_measurements();
        let verifier = NitroVerifier::new(measurements, vec![]);
        let doc = create_valid_attestation_doc();
        
        let attestation_result = verifier.verify_attestation(&doc).await.unwrap();
        let kms_config = KmsConfig::default();
        
        let token = generate_kms_token(&attestation_result, &kms_config).await.unwrap();
        assert!(!token.is_empty());
    }
}

