// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use crate::cert_v1::{write_cert_with_binding, CertV1, MorphInfo};
use crate::policy_adapter::{
    self, EnforcementMode, PermissionResult, PolicyAdapter, PolicyConfig, Tool,
};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use tracing::{error, info, warn}; // for naming consistency in docs

/// Runtime event that triggers permitD evaluation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeEvent {
    pub event_id: String,
    pub event_type: String, // "call", "read", "write", "log", "declassify", "emit"
    pub user_id: String,
    pub roles: Vec<String>,
    pub organization: String,
    pub session_id: String,
    pub epoch: u64,
    pub attributes: Vec<(String, String)>,
    pub tenant: String,
    pub timestamp: u64,

    // Resource-specific fields
    pub resource_uri: Option<String>,
    pub resource_version: Option<u64>,
    pub field_path: Option<Vec<String>>,
    pub tool: Option<String>,
    pub args: Option<Vec<String>>,

    // Witness and label information
    pub merkle_witness: Option<String>,
    pub field_commit: Option<String>,
    pub source_label: Option<String>,
    pub target_label: Option<String>,
}

/// PermitD enforcement hook result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnforcementResult {
    pub event_id: String,
    pub allowed: bool,
    pub reason: String,
    pub epoch: u64,
    pub path_witness_ok: bool,
    pub label_derivation_ok: bool,
    pub permit_decision: String,
    pub enforcement_mode: String,
    pub timestamp: u64,
}

/// PermitD enforcement hook that evaluates every runtime event
pub struct PermitEnforcementHook {
    policy_adapter: PolicyAdapter,
    enforcement_stats: EnforcementStats,
    feature_flags: HashMap<String, bool>,
    enabled_tools: HashSet<String>,
}

/// Enforcement statistics
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct EnforcementStats {
    pub total_events: u64,
    pub allowed_events: u64,
    pub denied_events: u64,
    pub call_events: u64,
    pub read_events: u64,
    pub write_events: u64,
    pub log_events: u64,
    pub declassify_events: u64,
    pub emit_events: u64,
    pub violations_recorded: u64,
}


impl PermitEnforcementHook {
    pub fn new(config: PolicyConfig) -> Self {
        let mut feature_flags = HashMap::new();
        feature_flags.insert("permit_enforcement".to_string(), true);
        feature_flags.insert("witness_validation".to_string(), true);
        feature_flags.insert("label_derivation".to_string(), true);
        feature_flags.insert("epoch_validation".to_string(), true);

        Self {
            policy_adapter: PolicyAdapter::new(config),
            enforcement_stats: EnforcementStats::default(),
            feature_flags,
            enabled_tools: Self::load_enabled_tools(),
        }
    }

    fn load_enabled_tools() -> HashSet<String> {
        let mut enabled = HashSet::new();
        for tool in crate::env_config::enabled_tools_override() {
            enabled.insert(tool);
        }
        let allowlist_paths = [
            "policy/allowlist.json",
            "runtime/sidecar-watcher/policy/allowlist.json",
        ];
        for path in allowlist_paths {
            if let Ok(data) = fs::read_to_string(path) {
                if let Ok(json) = serde_json::from_str::<serde_json::Value>(&data) {
                    if let Some(tools) = json.get("tools").and_then(|t| t.as_object()) {
                        for (name, entry) in tools {
                            let can_use = entry
                                .get("can_use")
                                .and_then(|v| v.as_bool())
                                .unwrap_or(false);
                            if can_use {
                                enabled.insert(name.clone());
                            }
                        }
                    }
                }
                break;
            }
        }
        // Dev fallback: known platform tools when manifest has default_deny entries.
        if enabled.is_empty() && !crate::env_config::is_production_profile() {
            for tool in [
                "SendEmail",
                "LogSpend",
                "LogAction",
                "NetworkCall",
                "ReadFile",
                "DatabaseQuery",
            ] {
                enabled.insert(tool.to_string());
            }
        }
        enabled
    }

    /// Process a runtime event and enforce permitD
    pub fn process_event(&mut self, event: &RuntimeEvent) -> Result<EnforcementResult> {
        self.enforcement_stats.total_events += 1;

        // Update event type counters
        match event.event_type.as_str() {
            "call" => self.enforcement_stats.call_events += 1,
            "read" => self.enforcement_stats.read_events += 1,
            "write" => self.enforcement_stats.write_events += 1,
            "log" => self.enforcement_stats.log_events += 1,
            "declassify" => self.enforcement_stats.declassify_events += 1,
            "emit" => self.enforcement_stats.emit_events += 1,
            _ => {}
        }

        // Convert to policy adapter RuntimeEvent format
        let policy_event = self.convert_to_policy_event(event);

        // Evaluate permission using policy adapter
        let permission_result = self.policy_adapter.process_event(&policy_event);

        // Update enforcement statistics
        if permission_result.allowed {
            self.enforcement_stats.allowed_events += 1;
        } else {
            self.enforcement_stats.denied_events += 1;
            self.enforcement_stats.violations_recorded += 1;
        }

        // Create enforcement result
        let enforcement_result = EnforcementResult {
            event_id: event.event_id.clone(),
            allowed: permission_result.allowed,
            reason: permission_result.reason.clone(),
            epoch: permission_result.epoch,
            path_witness_ok: permission_result.path_witness_ok,
            label_derivation_ok: permission_result.label_derivation_ok,
            permit_decision: permission_result.permit_decision.clone(),
            enforcement_mode: self.get_enforcement_mode_string(),
            timestamp: event.timestamp,
        };

        // Log enforcement decision
        if permission_result.allowed {
            info!(
                "Event {} permitted: {}",
                event.event_id, permission_result.reason
            );
        } else {
            warn!(
                "Event {} denied: {}",
                event.event_id, permission_result.reason
            );
            self.record_violation(event, &permission_result);
        }

        // Emit CERT-V1 on emit events and at end-like events we treat as emit_end
        if event.event_type == "emit" {
            if let Err(e) = self.emit_cert_v1(event, &enforcement_result) {
                warn!("Failed to emit CERT-V1: {}", e);
            }
        }

        Ok(enforcement_result)
    }

    fn emit_cert_v1(&self, event: &RuntimeEvent, result: &EnforcementResult) -> Result<()> {
        // Gather environment/config for required fields
        let bundle_id = std::env::var("BUNDLE_ID").unwrap_or_else(|_| {
            "sha256:0000000000000000000000000000000000000000000000000000000000000000".to_string()
        });
        let policy_hash = std::env::var("POLICY_HASH").unwrap_or_default();
        let proof_hash = std::env::var("PROOF_HASH").unwrap_or_default();
        let automata_hash = std::env::var("AUTOMATA_HASH").unwrap_or_default();
        let labeler_hash = std::env::var("LABELER_HASH").unwrap_or_default();
        let sidecar_build = std::env::var("SIDECAR_BUILD").unwrap_or_else(|_| "dev".to_string());
        let egress_profile =
            std::env::var("EGRESS_PROFILE").unwrap_or_else(|_| "EGRESS-DET-P1@1.0".to_string());
        let morph_block = if let (Ok(env_digest), Ok(branch_id), Ok(base_image)) = (
            std::env::var("MORPH_ENV_SNAPSHOT_DIGEST"),
            std::env::var("MORPH_BRANCH_ID"),
            std::env::var("MORPH_BASE_IMAGE"),
        ) {
            Some(MorphInfo {
                env_snapshot_digest: env_digest,
                branch_id,
                base_image,
                morphvm_id: std::env::var("MORPHVM_ID").ok(),
            })
        } else {
            None
        };

        // Map NI monitor verdict from feature flags or default
        let ni_monitor = if result.allowed { "accept" } else { "reject" }.to_string();

        // CERT signature: set CERT_SIG for real DSSE sig, or leave unset for unconfigured (no placeholder)
        let sig = std::env::var("CERT_SIG").unwrap_or_else(|_| "unconfigured".to_string());

        let cert = CertV1 {
            bundle_id,
            policy_hash,
            proof_hash,
            automata_hash,
            labeler_hash,
            ni_monitor,
            permit_decision: result.permit_decision.clone(),
            path_witness_ok: result.path_witness_ok,
            label_derivation_ok: result.label_derivation_ok,
            epoch: result.epoch,
            sidecar_build,
            egress_profile,
            morph: morph_block,
            sig,
        };

        // Use session and seq from event context; fallback defaults
        let session = &event.session_id;
        let seq = result.timestamp; // fallback; ideally monotonic seq

        let bundle_ref = std::env::var("EVIDENCE_BUNDLE_REF").ok();
        let path = write_cert_with_binding(&cert, session, seq, bundle_ref.as_deref())?;
        info!("CERT-V1 written with Evidence v0.1 binding: {}", path);
        Ok(())
    }

    /// Process call event with tool validation
    pub fn process_call_event(&mut self, event: &RuntimeEvent) -> Result<EnforcementResult> {
        // Validate tool exists and is enabled
        if let Some(ref tool) = event.tool {
            if !self.is_tool_enabled(tool) {
                return Ok(EnforcementResult {
                    event_id: event.event_id.clone(),
                    allowed: false,
                    reason: format!("Tool '{}' is not enabled", tool),
                    epoch: self.policy_adapter.get_current_epoch(),
                    path_witness_ok: true,
                    label_derivation_ok: true,
                    permit_decision: "reject".to_string(),
                    enforcement_mode: self.get_enforcement_mode_string(),
                    timestamp: event.timestamp,
                });
            }
        }

        self.process_event(event)
    }

    /// Process read event with witness validation
    pub fn process_read_event(&mut self, event: &RuntimeEvent) -> Result<EnforcementResult> {
        // Validate Merkle path witness if in high assurance mode
        if *self
            .feature_flags
            .get("witness_validation")
            .unwrap_or(&false)
        {
            if let Some(ref witness) = event.merkle_witness {
                if !self.validate_merkle_witness(witness, &event.field_path) {
                    return Ok(EnforcementResult {
                        event_id: event.event_id.clone(),
                        allowed: false,
                        reason: "Invalid Merkle path witness".to_string(),
                        epoch: self.policy_adapter.get_current_epoch(),
                        path_witness_ok: false,
                        label_derivation_ok: true,
                        permit_decision: "reject".to_string(),
                        enforcement_mode: self.get_enforcement_mode_string(),
                        timestamp: event.timestamp,
                    });
                }
            } else {
                return Ok(EnforcementResult {
                    event_id: event.event_id.clone(),
                    allowed: false,
                    reason: "Missing Merkle path witness".to_string(),
                    epoch: self.policy_adapter.get_current_epoch(),
                    path_witness_ok: false,
                    label_derivation_ok: true,
                    permit_decision: "reject".to_string(),
                    enforcement_mode: self.get_enforcement_mode_string(),
                    timestamp: event.timestamp,
                });
            }
        }

        self.process_event(event)
    }

    /// Process write event with witness and label validation
    pub fn process_write_event(&mut self, event: &RuntimeEvent) -> Result<EnforcementResult> {
        // Validate Merkle path witness
        if *self
            .feature_flags
            .get("witness_validation")
            .unwrap_or(&false)
        {
            if let Some(ref witness) = event.merkle_witness {
                if !self.validate_merkle_witness(witness, &event.field_path) {
                    return Ok(EnforcementResult {
                        event_id: event.event_id.clone(),
                        allowed: false,
                        reason: "Invalid Merkle path witness".to_string(),
                        epoch: self.policy_adapter.get_current_epoch(),
                        path_witness_ok: false,
                        label_derivation_ok: true,
                        permit_decision: "reject".to_string(),
                        enforcement_mode: self.get_enforcement_mode_string(),
                        timestamp: event.timestamp,
                    });
                }
            } else {
                return Ok(EnforcementResult {
                    event_id: event.event_id.clone(),
                    allowed: false,
                    reason: "Missing Merkle path witness".to_string(),
                    epoch: self.policy_adapter.get_current_epoch(),
                    path_witness_ok: false,
                    label_derivation_ok: true,
                    permit_decision: "reject".to_string(),
                    enforcement_mode: self.get_enforcement_mode_string(),
                    timestamp: event.timestamp,
                });
            }
        }

        // Validate label derivation
        if *self.feature_flags.get("label_derivation").unwrap_or(&false) {
            if let (Some(ref source), Some(ref target)) = (&event.source_label, &event.target_label)
            {
                if !self.validate_label_derivation(source, target) {
                    return Ok(EnforcementResult {
                        event_id: event.event_id.clone(),
                        allowed: false,
                        reason: "Invalid label derivation".to_string(),
                        epoch: self.policy_adapter.get_current_epoch(),
                        path_witness_ok: true,
                        label_derivation_ok: false,
                        permit_decision: "reject".to_string(),
                        enforcement_mode: self.get_enforcement_mode_string(),
                        timestamp: event.timestamp,
                    });
                }
            }
        }

        self.process_event(event)
    }

    /// Process declassify event with label flow validation
    pub fn process_declassify_event(&mut self, event: &RuntimeEvent) -> Result<EnforcementResult> {
        // Validate declassification rules
        if let (Some(ref source), Some(ref target)) = (&event.source_label, &event.target_label) {
            if !self.validate_declassification(source, target, &event.attributes) {
                return Ok(EnforcementResult {
                    event_id: event.event_id.clone(),
                    allowed: false,
                    reason: "Declassification rule violation".to_string(),
                    epoch: self.policy_adapter.get_current_epoch(),
                    path_witness_ok: true,
                    label_derivation_ok: false,
                    permit_decision: "reject".to_string(),
                    enforcement_mode: self.get_enforcement_mode_string(),
                    timestamp: event.timestamp,
                });
            }
        }

        self.process_event(event)
    }

    /// Validate Merkle path witness
    fn validate_merkle_witness(&self, witness: &str, _field_path: &Option<Vec<String>>) -> bool {
        // Require non-empty witness until full crypto validation is wired
        !witness.is_empty()
    }

    /// Validate label derivation
    fn validate_label_derivation(&self, source: &str, target: &str) -> bool {
        // Minimal check until IFC derivation rules are wired
        source != target
    }

    /// Validate declassification rules
    fn validate_declassification(
        &self,
        source: &str,
        target: &str,
        _attributes: &[(String, String)],
    ) -> bool {
        // Minimal check until declassification rules are wired
        source != target
    }

    /// Check if a tool is enabled
    fn is_tool_enabled(&self, tool: &str) -> bool {
        self.enabled_tools.contains(tool)
    }

    /// Get enforcement mode as string
    fn get_enforcement_mode_string(&self) -> String {
        match self.policy_adapter.get_enforcement_mode() {
            EnforcementMode::Enforce => "enforce".to_string(),
            EnforcementMode::Shadow => "shadow".to_string(),
            EnforcementMode::Monitor => "monitor".to_string(),
        }
    }

    /// Record a policy violation
    fn record_violation(&mut self, event: &RuntimeEvent, result: &PermissionResult) {
        let violation = ViolationRecord {
            event_id: event.event_id.clone(),
            user_id: event.user_id.clone(),
            event_type: event.event_type.clone(),
            reason: result.reason.clone(),
            epoch: result.epoch,
            timestamp: event.timestamp,
            attributes: event.attributes.clone(),
        };

        // Log violation
        error!("Policy violation recorded: {:?}", violation);

        // In a real implementation, this would be sent to a violation tracking system
        // or stored in a database for audit purposes
    }

    /// Get enforcement statistics
    pub fn get_stats(&self) -> &EnforcementStats {
        &self.enforcement_stats
    }

    /// Reset enforcement statistics
    pub fn reset_stats(&mut self) {
        self.enforcement_stats = EnforcementStats::default();
    }

    /// Update feature flags
    pub fn update_feature_flags(&mut self, flags: HashMap<String, bool>) {
        self.feature_flags = flags;
    }

    /// Convert permit enforcement RuntimeEvent to policy adapter RuntimeEvent
    fn convert_to_policy_event(&self, event: &RuntimeEvent) -> policy_adapter::RuntimeEvent {
        policy_adapter::RuntimeEvent {
            event_type: event.event_type.clone(),
            user_id: event.user_id.clone(),
            roles: event.roles.clone(),
            organization: event.organization.clone(),
            session_id: event.session_id.clone(),
            epoch: event.epoch,
            attributes: event.attributes.clone(),
            tenant: event.tenant.clone(),
            timestamp: event.timestamp,
            tool: event.tool.as_ref().map(|t| match t.as_str() {
                "SendEmail" => Tool::SendEmail,
                "FileRead" => Tool::FileRead,
                "FileWrite" => Tool::FileWrite,
                "DatabaseQuery" => Tool::DatabaseQuery,
                _ => Tool::SendEmail, // default fallback
            }),
            resource_uri: event.resource_uri.clone().unwrap_or_default(),
            resource_version: event.resource_version,
            field_path: event.field_path.clone(),
        }
    }
}

/// Violation record for audit purposes
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ViolationRecord {
    pub event_id: String,
    pub user_id: String,
    pub event_type: String,
    pub reason: String,
    pub epoch: u64,
    pub timestamp: u64,
    pub attributes: Vec<(String, String)>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permit_enforcement_hook_creation() {
        let config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: true,
            feature_flags: HashMap::new(),
        };

        let hook = PermitEnforcementHook::new(config);
        assert_eq!(hook.enforcement_stats.total_events, 0);
    }

    #[test]
    fn test_call_event_processing() {
        let config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: false,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut hook = PermitEnforcementHook::new(config);

        let event = RuntimeEvent {
            event_id: "test-1".to_string(),
            event_type: "call".to_string(),
            user_id: "test-user".to_string(),
            roles: vec!["admin".to_string()],
            organization: "test-org".to_string(),
            session_id: "session-1".to_string(),
            epoch: 1,
            attributes: vec![("permission".to_string(), "call".to_string())],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
            resource_uri: None,
            resource_version: None,
            field_path: None,
            tool: Some("SendEmail".to_string()),
            args: Some(vec!["test@example.com".to_string()]),
            merkle_witness: None,
            field_commit: None,
            source_label: None,
            target_label: None,
        };

        let result = hook.process_call_event(&event).unwrap();
        assert!(result.allowed);
        assert_eq!(result.permit_decision, "accept");
    }
}
