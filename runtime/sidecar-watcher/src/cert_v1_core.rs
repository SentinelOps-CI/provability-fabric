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

use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// CERT-V1 Core Certificate (Hot Path)
///
/// Minimal certificate containing only essential fields for performance-critical paths.
/// This is the compact core that gets generated synchronously during decision processing.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertV1Core {
    /// Bundle identifier
    pub bundle_id: String,

    /// Sequence number for ordering
    pub seq: u64,

    /// Policy hash for verification
    pub policy_hash: String,

    /// Proof hash for verification
    pub proof_hash: String,

    /// Automata hash for verification
    pub automata_hash: String,

    /// Labeler hash for verification
    pub labeler_hash: String,

    /// Non-interference monitor result
    pub ni_monitor: String, // "inapplicable" | "accept" | "reject" | "error"

    /// Epoch for time-based access control
    pub epoch: u64,

    /// Short reason code for quick decision understanding
    pub reason_code: String,

    /// Timestamp of certificate generation
    pub timestamp: u64,

    /// Tenant identifier
    pub tenant_id: String,

    /// Session identifier
    pub session_id: String,
}

impl CertV1Core {
    /// Create a new core certificate
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        bundle_id: String,
        seq: u64,
        policy_hash: String,
        proof_hash: String,
        automata_hash: String,
        labeler_hash: String,
        ni_monitor: String,
        epoch: u64,
        reason_code: String,
        tenant_id: String,
        session_id: String,
    ) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            bundle_id,
            seq,
            policy_hash,
            proof_hash,
            automata_hash,
            labeler_hash,
            ni_monitor,
            epoch,
            reason_code,
            timestamp: now,
            tenant_id,
            session_id,
        }
    }

    /// Get certificate size in bytes (for performance monitoring)
    pub fn size_bytes(&self) -> usize {
        // Approximate size calculation
        self.bundle_id.len()
            + self.policy_hash.len()
            + self.proof_hash.len()
            + self.automata_hash.len()
            + self.labeler_hash.len()
            + self.ni_monitor.len()
            + self.reason_code.len()
            + self.tenant_id.len()
            + self.session_id.len()
            + 64 // Fixed overhead for u64 fields and structure
    }

    /// Validate core certificate fields
    pub fn validate(&self) -> Result<(), String> {
        if self.bundle_id.is_empty() {
            return Err("bundle_id cannot be empty".to_string());
        }
        if self.policy_hash.is_empty() {
            return Err("policy_hash cannot be empty".to_string());
        }
        if self.proof_hash.is_empty() {
            return Err("proof_hash cannot be empty".to_string());
        }
        if self.automata_hash.is_empty() {
            return Err("automata_hash cannot be empty".to_string());
        }
        if self.labeler_hash.is_empty() {
            return Err("labeler_hash cannot be empty".to_string());
        }

        // Validate ni_monitor values
        let valid_ni_monitor = ["inapplicable", "accept", "reject", "error"];
        if !valid_ni_monitor.contains(&self.ni_monitor.as_str()) {
            return Err(format!("invalid ni_monitor value: {}", self.ni_monitor));
        }

        if self.tenant_id.is_empty() {
            return Err("tenant_id cannot be empty".to_string());
        }
        if self.session_id.is_empty() {
            return Err("session_id cannot be empty".to_string());
        }

        Ok(())
    }

    /// Convert to JSON for storage/transmission
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Create from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

impl Default for CertV1Core {
    fn default() -> Self {
        Self {
            bundle_id: String::new(),
            seq: 0,
            policy_hash: String::new(),
            proof_hash: String::new(),
            automata_hash: String::new(),
            labeler_hash: String::new(),
            ni_monitor: "inapplicable".to_string(),
            epoch: 0,
            reason_code: String::new(),
            timestamp: 0,
            tenant_id: String::new(),
            session_id: String::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_core_cert_creation() {
        let cert = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        assert_eq!(cert.bundle_id, "bundle-123");
        assert_eq!(cert.seq, 1);
        assert_eq!(cert.ni_monitor, "accept");
        assert_eq!(cert.epoch, 42);
        assert_eq!(cert.reason_code, "PERMIT");
    }

    #[test]
    fn test_core_cert_validation() {
        let mut cert = CertV1Core::default();
        cert.bundle_id = "bundle-123".to_string();
        cert.policy_hash = "policy-hash".to_string();
        cert.proof_hash = "proof-hash".to_string();
        cert.automata_hash = "automata-hash".to_string();
        cert.labeler_hash = "labeler-hash".to_string();
        cert.ni_monitor = "accept".to_string();
        cert.tenant_id = "tenant-1".to_string();
        cert.session_id = "session-1".to_string();

        assert!(cert.validate().is_ok());
    }

    #[test]
    fn test_core_cert_validation_invalid_ni_monitor() {
        let mut cert = CertV1Core::default();
        cert.bundle_id = "bundle-123".to_string();
        cert.policy_hash = "policy-hash".to_string();
        cert.proof_hash = "proof-hash".to_string();
        cert.automata_hash = "automata-hash".to_string();
        cert.labeler_hash = "labeler-hash".to_string();
        cert.ni_monitor = "invalid".to_string();
        cert.tenant_id = "tenant-1".to_string();
        cert.session_id = "session-1".to_string();

        assert!(cert.validate().is_err());
    }

    #[test]
    fn test_core_cert_json_serialization() {
        let cert = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let json = cert.to_json().unwrap();
        let deserialized = CertV1Core::from_json(&json).unwrap();

        assert_eq!(cert.bundle_id, deserialized.bundle_id);
        assert_eq!(cert.seq, deserialized.seq);
        assert_eq!(cert.ni_monitor, deserialized.ni_monitor);
    }

    #[test]
    fn test_core_cert_size_calculation() {
        let cert = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let size = cert.size_bytes();
        assert!(size > 0);
        assert!(size < 1000); // Should be small for hot path
    }
}
