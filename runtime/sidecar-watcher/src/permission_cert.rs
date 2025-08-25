// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// Enhanced permission certificate with evidence and NI alignment
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionCertificate {
    pub metadata: PermissionCertMetadata,
    pub permission_evidence: PermissionEvidence,
    pub ni_monitor_evidence: NIMonitorEvidence,
    pub bridge_guarantee: BridgeGuarantee,
    pub signature: Option<CertificateSignature>,
}

/// Permission certificate metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionCertMetadata {
    pub certificate_id: String,
    pub session_id: String,
    pub bundle_id: String,
    pub plan_hash: String,
    pub created_at: u64,
    pub expires_at: u64,
    pub issuer: String,
    pub version: String,
    pub epoch: u64,
}

/// Permission evidence for each event
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionEvidence {
    pub events: Vec<PermissionEvent>,
    pub overall_decision: String, // "accept", "reject", "error"
    pub epoch: u64,
    pub policy_hash: String,
    pub permitd_hash: String,
}

/// Individual permission event evidence
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionEvent {
    pub event_id: String,
    pub event_type: EventType,
    pub timestamp: u64,
    pub principal: Principal,
    pub action: Action,
    pub context: Context,
    pub permit_decision: String, // "accept", "reject", "error"
    pub path_witness_ok: bool,
    pub label_derivation_ok: bool,
    pub epoch: u64,
    pub reasoning: String,
    pub attributes: HashMap<String, String>,
}

/// Event types that can be permission-checked
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum EventType {
    Call,
    Return,
    Log,
    Declassify,
    Emit,
    Read,
    Write,
}

/// Principal information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Principal {
    pub id: String,
    pub roles: Vec<String>,
    pub org: String,
    pub tenant: String,
}

/// Action information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Action {
    pub action_type: String,
    pub resource: String,
    pub path: Option<Vec<String>>,
    pub parameters: HashMap<String, String>,
}

/// Context information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Context {
    pub session: String,
    pub epoch: u64,
    pub attributes: Vec<(String, String)>,
    pub tenant: String,
    pub timestamp: u64,
}

/// Non-interference monitor evidence
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIMonitorEvidence {
    pub ni_monitor_hash: String,
    pub automata_hash: String,
    pub labeler_hash: String,
    pub prefix_count: usize,
    pub verification_time_ms: u64,
    pub confidence: f64,
    pub violations: Vec<String>,
    pub bridge_theorem_reference: String, // "Theorem~ni-bridge"
}

/// Bridge guarantee linking local checks to global NI
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeGuarantee {
    pub theorem_reference: String, // "Theorem~ni-bridge"
    pub local_checks_ok: bool,
    pub global_ni_ok: bool,
    pub proof_hash: String,
    pub guarantee_text: String,
}

/// Certificate signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertificateSignature {
    pub algorithm: String,
    pub signature: String,
    pub public_key: String,
    pub timestamp: u64,
}

impl PermissionCertificate {
    /// Create a new permission certificate
    pub fn new(session_id: String, bundle_id: String, plan_hash: String, epoch: u64) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            metadata: PermissionCertMetadata {
                certificate_id: Self::generate_cert_id(),
                session_id,
                bundle_id,
                plan_hash,
                created_at: now,
                expires_at: now + 3600, // 1 hour TTL
                issuer: "provability-fabric".to_string(),
                version: "v2.0".to_string(),
                epoch,
            },
            permission_evidence: PermissionEvidence {
                events: Vec::new(),
                overall_decision: "accept".to_string(),
                epoch,
                policy_hash: String::new(),
                permitd_hash: String::new(),
            },
            ni_monitor_evidence: NIMonitorEvidence {
                ni_monitor_hash: String::new(),
                automata_hash: String::new(),
                labeler_hash: String::new(),
                prefix_count: 0,
                verification_time_ms: 0,
                confidence: 1.0,
                violations: Vec::new(),
                bridge_theorem_reference: "Theorem~ni-bridge".to_string(),
            },
            bridge_guarantee: BridgeGuarantee {
                theorem_reference: "Theorem~ni-bridge".to_string(),
                local_checks_ok: true,
                global_ni_ok: true,
                proof_hash: String::new(),
                guarantee_text: "Bridge guarantee: Local permitD + \\MonNI acceptance implies global Non-Interference".to_string(),
            },
            signature: None,
        }
    }

    /// Add a permission event to the certificate
    pub fn add_permission_event(&mut self, event: PermissionEvent) {
        self.permission_evidence.events.push(event);
        self.update_overall_decision();
    }

    /// Update the overall decision based on all events
    fn update_overall_decision(&mut self) {
        let has_reject = self
            .permission_evidence
            .events
            .iter()
            .any(|e| e.permit_decision == "reject");
        let has_error = self
            .permission_evidence
            .events
            .iter()
            .any(|e| e.permit_decision == "error");

        self.permission_evidence.overall_decision = if has_error {
            "error".to_string()
        } else if has_reject {
            "reject".to_string()
        } else {
            "accept".to_string()
        };
    }

    /// Set the NI monitor evidence
    pub fn set_ni_monitor_evidence(&mut self, evidence: NIMonitorEvidence) {
        self.ni_monitor_evidence = evidence;
    }

    /// Set the bridge guarantee
    pub fn set_bridge_guarantee(&mut self, guarantee: BridgeGuarantee) {
        self.bridge_guarantee = guarantee;
    }

    /// Generate a unique certificate ID
    fn generate_cert_id() -> String {
        let mut hasher = Sha256::new();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        hasher.update(timestamp.to_string().as_bytes());
        format!("cert_{:x}", hasher.finalize())
    }

    /// Calculate the certificate hash
    pub fn calculate_hash(&self) -> String {
        let mut hasher = Sha256::new();
        let cert_data = serde_json::to_string(self).unwrap();
        hasher.update(cert_data.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Validate the certificate
    pub fn validate(&self) -> Result<(), String> {
        // Check if certificate has expired
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if now > self.metadata.expires_at {
            return Err("Certificate has expired".to_string());
        }

        // Check if all required fields are present
        if self.permission_evidence.events.is_empty() {
            return Err("No permission events found".to_string());
        }

        // Check if NI monitor evidence is present
        if self.ni_monitor_evidence.ni_monitor_hash.is_empty() {
            return Err("NI monitor hash is missing".to_string());
        }

        // Check if bridge guarantee is present
        if self.bridge_guarantee.theorem_reference.is_empty() {
            return Err("Bridge theorem reference is missing".to_string());
        }

        Ok(())
    }

    /// Convert to JSON string
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Create from JSON string
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

/// Builder for permission events
pub struct PermissionEventBuilder {
    event: PermissionEvent,
}

impl PermissionEventBuilder {
    /// Create a new event builder
    pub fn new(event_type: EventType, principal: Principal, action: Action) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            event: PermissionEvent {
                event_id: Self::generate_event_id(),
                event_type,
                timestamp: now,
                principal,
                action,
                context: Context {
                    session: String::new(),
                    epoch: 0,
                    attributes: Vec::new(),
                    tenant: String::new(),
                    timestamp: now,
                },
                permit_decision: "accept".to_string(),
                path_witness_ok: true,
                label_derivation_ok: true,
                epoch: 0,
                reasoning: String::new(),
                attributes: HashMap::new(),
            },
        }
    }

    /// Set the context
    pub fn context(mut self, context: Context) -> Self {
        self.event.context = context;
        self.event.epoch = context.epoch;
        self
    }

    /// Set the permission decision
    pub fn decision(mut self, decision: String) -> Self {
        self.event.permit_decision = decision;
        self
    }

    /// Set witness validation status
    pub fn witness_status(mut self, path_ok: bool, label_ok: bool) -> Self {
        self.event.path_witness_ok = path_ok;
        self.event.label_derivation_ok = label_ok;
        self
    }

    /// Set reasoning
    pub fn reasoning(mut self, reasoning: String) -> Self {
        self.event.reasoning = reasoning;
        self
    }

    /// Add attribute
    pub fn attribute(mut self, key: String, value: String) -> Self {
        self.event.attributes.insert(key, value);
        self
    }

    /// Build the event
    pub fn build(self) -> PermissionEvent {
        self.event
    }

    /// Generate a unique event ID
    fn generate_event_id() -> String {
        let mut hasher = Sha256::new();
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        hasher.update(timestamp.to_string().as_bytes());
        format!("event_{:x}", hasher.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_certificate_creation() {
        let cert = PermissionCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            1,
        );

        assert_eq!(cert.metadata.session_id, "session-1");
        assert_eq!(cert.metadata.bundle_id, "bundle-1");
        assert_eq!(cert.metadata.epoch, 1);
        assert_eq!(cert.permission_evidence.overall_decision, "accept");
    }

    #[test]
    fn test_permission_event_builder() {
        let principal = Principal {
            id: "user-1".to_string(),
            roles: vec!["reader".to_string()],
            org: "org-1".to_string(),
            tenant: "tenant-1".to_string(),
        };

        let action = Action {
            action_type: "read".to_string(),
            resource: "doc-1".to_string(),
            path: Some(vec!["field1".to_string()]),
            parameters: HashMap::new(),
        };

        let context = Context {
            session: "session-1".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "A".to_string())],
            tenant: "tenant-1".to_string(),
            timestamp: 1234567890,
        };

        let event = PermissionEventBuilder::new(EventType::Read, principal, action)
            .context(context)
            .decision("accept".to_string())
            .witness_status(true, true)
            .reasoning("User has read permission".to_string())
            .attribute("project".to_string(), "A".to_string())
            .build();

        assert_eq!(event.permit_decision, "accept");
        assert_eq!(event.epoch, 1);
        assert_eq!(event.context.session, "session-1");
        assert!(event.path_witness_ok);
        assert!(event.label_derivation_ok);
    }

    #[test]
    fn test_certificate_validation() {
        let mut cert = PermissionCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            1,
        );

        // Should fail validation initially (no events)
        assert!(cert.validate().is_err());

        // Add an event
        let principal = Principal {
            id: "user-1".to_string(),
            roles: vec!["reader".to_string()],
            org: "org-1".to_string(),
            tenant: "tenant-1".to_string(),
        };

        let action = Action {
            action_type: "read".to_string(),
            resource: "doc-1".to_string(),
            path: None,
            parameters: HashMap::new(),
        };

        let event = PermissionEventBuilder::new(EventType::Read, principal, action).build();

        cert.add_permission_event(event);

        // Should still fail (no NI monitor hash)
        assert!(cert.validate().is_err());

        // Set NI monitor evidence
        cert.ni_monitor_evidence.ni_monitor_hash = "hash-123".to_string();
        cert.bridge_guarantee.theorem_reference = "Theorem~ni-bridge".to_string();

        // Should now pass validation
        assert!(cert.validate().is_ok());
    }

    #[test]
    fn test_overall_decision_update() {
        let mut cert = PermissionCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            1,
        );

        // Add accept event
        let principal = Principal {
            id: "user-1".to_string(),
            roles: vec!["reader".to_string()],
            org: "org-1".to_string(),
            tenant: "tenant-1".to_string(),
        };

        let action = Action {
            action_type: "read".to_string(),
            resource: "doc-1".to_string(),
            path: None,
            parameters: HashMap::new(),
        };

        let event = PermissionEventBuilder::new(EventType::Read, principal, action)
            .decision("accept".to_string())
            .build();

        cert.add_permission_event(event);
        assert_eq!(cert.permission_evidence.overall_decision, "accept");

        // Add reject event
        let event2 = PermissionEventBuilder::new(EventType::Read, principal, action)
            .decision("reject".to_string())
            .build();

        cert.add_permission_event(event2);
        assert_eq!(cert.permission_evidence.overall_decision, "reject");

        // Add error event
        let event3 = PermissionEventBuilder::new(EventType::Read, principal, action)
            .decision("error".to_string())
            .build();

        cert.add_permission_event(event3);
        assert_eq!(cert.permission_evidence.overall_decision, "error");
    }
}
