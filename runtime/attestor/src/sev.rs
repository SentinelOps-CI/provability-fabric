// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tracing::{info, warn, error};
use sha2::{Sha256, Digest};
use base64::{Engine as _, engine::general_purpose::STANDARD as BASE64};

/// SEV attestation report structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SevAttestationReport {
    pub version: u32,
    pub guest_svn: u32,
    pub policy: SevPolicy,
    pub family_id: [u8; 16],
    pub image_id: [u8; 16],
    pub vmpl: u32,
    pub signature_algo: u32,
    pub platform_version: SevPlatformVersion,
    pub platform_info: u64,
    pub flags: u32,
    pub reserved: u32,
    pub report_data: [u8; 64],
    pub measurement: [u8; 48],
    pub host_data: [u8; 32],
    pub id_key_digest: [u8; 48],
    pub author_key_digest: [u8; 48],
    pub report_id: [u8; 32],
    pub report_id_ma: [u8; 32],
    pub reported_tcb: SevTcbVersion,
    pub reserved2: [u8; 32],
    pub chip_id: [u8; 64],
    pub committed_tcb: SevTcbVersion,
    pub current_build: u8,
    pub current_minor: u8,
    pub current_major: u8,
    pub current_build_id: u8,
    pub committed_build: u8,
    pub committed_minor: u8,
    pub committed_major: u8,
    pub committed_build_id: u8,
    pub launch_tcb: SevTcbVersion,
    pub reserved3: [u8; 168],
    pub signature: [u8; 512],
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SevPolicy {
    pub debug: bool,
    pub migratable: bool,
    pub smt: bool,
    pub reserved: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SevPlatformVersion {
    pub major: u8,
    pub minor: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SevTcbVersion {
    pub build: u8,
    pub minor: u8,
    pub major: u8,
    pub build_id: u8,
}

/// Expected SEV measurements
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SevMeasurements {
    pub expected_measurement: [u8; 48],
    pub expected_family_id: [u8; 16],
    pub expected_image_id: [u8; 16],
    pub expected_policy: SevPolicy,
    pub min_tcb_version: SevTcbVersion,
    pub max_age_seconds: u64,
}

/// SEV attestation verifier
pub struct SevVerifier {
    measurements: SevMeasurements,
    trusted_ark_cert: Vec<u8>,
    trusted_ask_cert: Vec<u8>,
}

impl SevVerifier {
    pub fn new(
        measurements: SevMeasurements,
        trusted_ark_cert: Vec<u8>,
        trusted_ask_cert: Vec<u8>,
    ) -> Self {
        Self {
            measurements,
            trusted_ark_cert,
            trusted_ask_cert,
        }
    }

    /// Verify a SEV attestation report
    pub async fn verify_attestation(
        &self,
        report: &SevAttestationReport,
    ) -> Result<AttestationResult> {
        // 1. Verify report signature
        if !self.verify_report_signature(report).await? {
            return Ok(AttestationResult::Invalid {
                reason: "Invalid signature".to_string(),
                details: "Report signature verification failed".to_string(),
            });
        }

        // 2. Verify measurement
        if report.measurement != self.measurements.expected_measurement {
            return Ok(AttestationResult::Invalid {
                reason: "Measurement mismatch".to_string(),
                details: "Platform measurement does not match expected value".to_string(),
            });
        }

        // 3. Verify family ID
        if report.family_id != self.measurements.expected_family_id {
            return Ok(AttestationResult::Invalid {
                reason: "Family ID mismatch".to_string(),
                details: "SEV family ID does not match expected value".to_string(),
            });
        }

        // 4. Verify image ID
        if report.image_id != self.measurements.expected_image_id {
            return Ok(AttestationResult::Invalid {
                reason: "Image ID mismatch".to_string(),
                details: "SEV image ID does not match expected value".to_string(),
            });
        }

        // 5. Verify policy
        if !self.verify_policy(&report.policy)? {
            return Ok(AttestationResult::Invalid {
                reason: "Policy violation".to_string(),
                details: "SEV policy does not meet security requirements".to_string(),
            });
        }

        // 6. Verify TCB version
        if !self.verify_tcb_version(&report.reported_tcb)? {
            return Ok(AttestationResult::Invalid {
                reason: "TCB version too old".to_string(),
                details: "Trusted Computing Base version is below minimum requirement".to_string(),
            });
        }

        // 7. Verify report age (if timestamp available in report_data)
        if let Some(report_timestamp) = self.extract_timestamp(report) {
            let current_time = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();

            if current_time - report_timestamp > self.measurements.max_age_seconds {
                return Ok(AttestationResult::Expired {
                    attested_at: report_timestamp,
                    current_time,
                });
            }
        }

        info!("SEV attestation verified successfully for image {:?}", report.image_id);

        Ok(AttestationResult::Valid {
            enclave_id: format!("sev-{:02x}{:02x}{:02x}{:02x}", 
                report.image_id[0], report.image_id[1], report.image_id[2], report.image_id[3]),
            measurements: self.extract_measurements_map(report),
            expires_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs() + self.measurements.max_age_seconds,
        })
    }

    /// Verify the report signature using AMD's public keys
    async fn verify_report_signature(&self, report: &SevAttestationReport) -> Result<bool> {
        // In production, this would verify the RSA signature using AMD's ARK/ASK certificates
        // For now, we'll implement a basic verification
        
        // Verify signature is not all zeros
        let all_zeros = [0u8; 512];
        if report.signature == all_zeros {
            return Ok(false);
        }

        // Verify signature length is correct
        if report.signature.len() != 512 {
            return Ok(false);
        }

        // In production, would verify against AMD's public keys
        // For now, just check that signature exists and is not zero
        Ok(true)
    }

    /// Verify SEV policy meets security requirements
    fn verify_policy(&self, policy: &SevPolicy) -> Result<bool> {
        // Debug mode should be disabled in production
        if policy.debug {
            warn!("SEV debug mode enabled - security risk");
            return Ok(false);
        }

        // SMT should be disabled for security isolation
        if policy.smt {
            warn!("SEV SMT enabled - potential security risk");
            return Ok(false);
        }

        Ok(true)
    }

    /// Verify TCB version meets minimum requirements
    fn verify_tcb_version(&self, reported_tcb: &SevTcbVersion) -> Result<bool> {
        let min_tcb = &self.measurements.min_tcb_version;

        // Compare TCB versions (major.minor.build.build_id)
        if reported_tcb.major < min_tcb.major {
            return Ok(false);
        }
        if reported_tcb.major == min_tcb.major && reported_tcb.minor < min_tcb.minor {
            return Ok(false);
        }
        if reported_tcb.major == min_tcb.major && reported_tcb.minor == min_tcb.minor && reported_tcb.build < min_tcb.build {
            return Ok(false);
        }
        if reported_tcb.major == min_tcb.major && reported_tcb.minor == min_tcb.minor && reported_tcb.build == min_tcb.build && reported_tcb.build_id < min_tcb.build_id {
            return Ok(false);
        }

        Ok(true)
    }

    /// Extract timestamp from report data if available
    fn extract_timestamp(&self, report: &SevAttestationReport) -> Option<u64> {
        // In production, this would parse the report_data field for a timestamp
        // For now, we'll assume the first 8 bytes contain a timestamp
        if report.report_data.len() >= 8 {
            let mut timestamp_bytes = [0u8; 8];
            timestamp_bytes.copy_from_slice(&report.report_data[0..8]);
            let timestamp = u64::from_le_bytes(timestamp_bytes);
            
            // Validate timestamp is reasonable (not too far in past/future)
            let current_time = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs();
            
            if timestamp > current_time + 3600 || timestamp < current_time - 86400 {
                return None; // Timestamp seems invalid
            }
            
            Some(timestamp)
        } else {
            None
        }
    }

    /// Extract measurements into a HashMap for compatibility
    fn extract_measurements_map(&self, report: &SevAttestationReport) -> HashMap<String, String> {
        let mut measurements = HashMap::new();
        
        measurements.insert("measurement".to_string(), hex::encode(report.measurement));
        measurements.insert("family_id".to_string(), hex::encode(report.family_id));
        measurements.insert("image_id".to_string(), hex::encode(report.image_id));
        measurements.insert("policy_debug".to_string(), report.policy.debug.to_string());
        measurements.insert("policy_migratable".to_string(), report.policy.migratable.to_string());
        measurements.insert("policy_smt".to_string(), report.policy.smt.to_string());
        measurements.insert("tcb_major".to_string(), report.reported_tcb.major.to_string());
        measurements.insert("tcb_minor".to_string(), report.reported_tcb.minor.to_string());
        measurements.insert("tcb_build".to_string(), report.reported_tcb.build.to_string());
        measurements.insert("tcb_build_id".to_string(), report.reported_tcb.build_id.to_string());
        
        measurements
    }
}

/// Attestation verification result (same as Nitro)
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

/// Generate short-lived KMS token for attested SEV enclave
pub async fn generate_sev_kms_token(
    attestation_result: &AttestationResult,
    kms_config: &SevKmsConfig,
) -> Result<String> {
    match attestation_result {
        AttestationResult::Valid { enclave_id, .. } => {
            let token_data = format!(
                "sev-enclave:{}:exp:{}:{}",
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

/// KMS configuration for SEV token generation
#[derive(Debug, Clone)]
pub struct SevKmsConfig {
    pub tenant_id: String,
    pub token_ttl_seconds: u64,
    pub max_key_operations: u32,
}

impl Default for SevKmsConfig {
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

    fn create_test_measurements() -> SevMeasurements {
        let mut expected_measurement = [0u8; 48];
        expected_measurement[0] = 0x12;
        expected_measurement[1] = 0x34;
        expected_measurement[2] = 0x56;

        let mut expected_family_id = [0u8; 16];
        expected_family_id[0] = 0xaa;
        expected_family_id[1] = 0xbb;

        let mut expected_image_id = [0u8; 16];
        expected_image_id[0] = 0xcc;
        expected_image_id[1] = 0xdd;

        SevMeasurements {
            expected_measurement,
            expected_family_id,
            expected_image_id,
            expected_policy: SevPolicy {
                debug: false,
                migratable: false,
                smt: false,
                reserved: 0,
            },
            min_tcb_version: SevTcbVersion {
                major: 0,
                minor: 0,
                build: 0,
                build_id: 0,
            },
            max_age_seconds: 3600,
        }
    }

    fn create_valid_sev_report() -> SevAttestationReport {
        let mut measurement = [0u8; 48];
        measurement[0] = 0x12;
        measurement[1] = 0x34;
        measurement[2] = 0x56;

        let mut family_id = [0u8; 16];
        family_id[0] = 0xaa;
        family_id[1] = 0xbb;

        let mut image_id = [0u8; 16];
        image_id[0] = 0xcc;
        image_id[1] = 0xdd;

        let mut report_data = [0u8; 64];
        let current_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        report_data[0..8].copy_from_slice(&current_time.to_le_bytes());

        let mut signature = [0u8; 512];
        signature[0] = 0x01; // Non-zero signature

        SevAttestationReport {
            version: 1,
            guest_svn: 0,
            policy: SevPolicy {
                debug: false,
                migratable: false,
                smt: false,
                reserved: 0,
            },
            family_id,
            image_id,
            vmpl: 0,
            signature_algo: 1,
            platform_version: SevPlatformVersion { major: 0, minor: 0 },
            platform_info: 0,
            flags: 0,
            reserved: 0,
            report_data,
            measurement,
            host_data: [0u8; 32],
            id_key_digest: [0u8; 48],
            author_key_digest: [0u8; 48],
            report_id: [0u8; 32],
            report_id_ma: [0u8; 32],
            reported_tcb: SevTcbVersion {
                major: 0,
                minor: 0,
                build: 0,
                build_id: 0,
            },
            reserved2: [0u8; 32],
            chip_id: [0u8; 64],
            committed_tcb: SevTcbVersion {
                major: 0,
                minor: 0,
                build: 0,
                build_id: 0,
            },
            current_build: 0,
            current_minor: 0,
            current_major: 0,
            current_build_id: 0,
            committed_build: 0,
            committed_minor: 0,
            committed_major: 0,
            committed_build_id: 0,
            launch_tcb: SevTcbVersion {
                major: 0,
                minor: 0,
                build: 0,
                build_id: 0,
            },
            reserved3: [0u8; 168],
            signature,
        }
    }

    #[tokio::test]
    async fn test_verify_valid_sev_attestation() {
        let measurements = create_test_measurements();
        let verifier = SevVerifier::new(measurements, vec![], vec![]);
        let report = create_valid_sev_report();

        let result = verifier.verify_attestation(&report).await.unwrap();
        
        match result {
            AttestationResult::Valid { enclave_id, .. } => {
                assert!(enclave_id.starts_with("sev-"));
            }
            _ => panic!("Expected valid attestation"),
        }
    }

    #[tokio::test]
    async fn test_verify_tampered_sev_report() {
        let measurements = create_test_measurements();
        let verifier = SevVerifier::new(measurements, vec![], vec![]);
        let mut report = create_valid_sev_report();
        
        // Tamper with the measurement
        report.measurement[0] = 0xff;

        let result = verifier.verify_attestation(&report).await.unwrap();
        
        match result {
            AttestationResult::Invalid { reason, .. } => {
                assert!(reason.contains("Measurement mismatch"));
            }
            _ => panic!("Expected invalid attestation"),
        }
    }

    #[tokio::test]
    async fn test_verify_debug_policy_violation() {
        let measurements = create_test_measurements();
        let verifier = SevVerifier::new(measurements, vec![], vec![]);
        let mut report = create_valid_sev_report();
        
        // Enable debug mode
        report.policy.debug = true;

        let result = verifier.verify_attestation(&report).await.unwrap();
        
        match result {
            AttestationResult::Invalid { reason, .. } => {
                assert!(reason.contains("Policy violation"));
            }
            _ => panic!("Expected invalid attestation"),
        }
    }

    #[tokio::test]
    async fn test_generate_sev_kms_token() {
        let measurements = create_test_measurements();
        let verifier = SevVerifier::new(measurements, vec![], vec![]);
        let report = create_valid_sev_report();
        
        let attestation_result = verifier.verify_attestation(&report).await.unwrap();
        let kms_config = SevKmsConfig::default();
        
        let token = generate_sev_kms_token(&attestation_result, &kms_config).await.unwrap();
        assert!(!token.is_empty());
    }
}

