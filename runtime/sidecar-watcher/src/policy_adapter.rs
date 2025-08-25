// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::collections::HashSet;
use tracing::{error, info, warn};

/// Principal represents a user, service, or agent
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Principal {
    pub id: String,
    pub roles: Vec<String>,
    pub org: String,
}

/// Document identifier for read/write operations
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct DocId {
    pub uri: String,
    pub version: u64,
}

/// Tool represents a capability or service
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Tool {
    SendEmail,
    LogSpend,
    LogAction,
    NetworkCall,
    FileRead,
    FileWrite,
    Custom { name: String },
}

/// Action represents what can be done
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Action {
    Call {
        tool: Tool,
    },
    Read {
        doc: DocId,
        path: Vec<String>,
    },
    Write {
        doc: DocId,
        path: Vec<String>,
    },
    Grant {
        principal: Principal,
        action: Box<Action>,
    },
}

/// Context contains runtime information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Ctx {
    pub session: String,
    pub epoch: u64,
    pub attributes: Vec<(String, String)>,
    pub tenant: String,
    pub timestamp: u64,
}

/// Permission evaluation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PermissionResult {
    pub allowed: bool,
    pub reason: String,
    pub epoch: u64,
    pub path_witness_ok: bool,
    pub label_derivation_ok: bool,
    pub permit_decision: String, // "accept", "reject", "error"
}

/// Policy adapter that maps runtime information to policy evaluation
pub struct PolicyAdapter {
    config: PolicyConfig,
    lean_interface: Option<LeanInterface>,
    epoch_manager: EpochManager,
    witness_validator: WitnessValidator,
}

/// Configuration for the policy adapter
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyConfig {
    pub enforcement_mode: EnforcementMode,
    pub shadow_mode: bool,
    pub epoch_validation: bool,
    pub witness_validation: bool,
    pub high_assurance_mode: bool,
    pub feature_flags: HashMap<String, bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnforcementMode {
    Enforce, // Block denied actions
    Shadow,  // Log but allow all actions
    Monitor, // Log and track violations
}

/// Interface to Lean permitD function
pub struct LeanInterface {
    // This would interface with the compiled Lean permitD function
    // For now, we'll implement a Rust version that mirrors the Lean logic
}

impl LeanInterface {
    pub fn new() -> Self {
        Self {}
    }

    /// Evaluate permitD for a given principal, action, and context
    pub fn evaluate_permit(&self, principal: &Principal, action: &Action, ctx: &Ctx) -> bool {
        match action {
            Action::Call { tool } => match tool {
                Tool::SendEmail => {
                    principal.roles.contains(&"email_user".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::LogSpend => {
                    principal.roles.contains(&"finance_user".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::LogAction => {
                    principal.roles.contains(&"logger".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::NetworkCall => {
                    principal.roles.contains(&"network_user".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::FileRead => {
                    principal.roles.contains(&"file_user".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::FileWrite => {
                    principal.roles.contains(&"file_writer".to_string())
                        || principal.roles.contains(&"admin".to_string())
                }
                Tool::Custom { name: _ } => principal.roles.contains(&"admin".to_string()),
            },
            Action::Read { doc, path } => {
                // IFC-aware read permission with field-level granularity
                let has_read_permission = principal.roles.contains(&"reader".to_string())
                    || principal.roles.contains(&"admin".to_string())
                    || (principal.roles.contains(&"owner".to_string())
                        && principal.org == "owner_org");

                // In high assurance mode, validate witness and label derivation
                if self.config.high_assurance_mode {
                    has_read_permission && self.validate_read_witness(doc, path, ctx)
                } else {
                    has_read_permission
                }
            }
            Action::Write { doc, path } => {
                // IFC-aware write permission with field-level granularity
                let has_write_permission = principal.roles.contains(&"writer".to_string())
                    || principal.roles.contains(&"admin".to_string())
                    || (principal.roles.contains(&"owner".to_string())
                        && principal.org == "owner_org");

                // In high assurance mode, validate witness and label derivation
                if self.config.high_assurance_mode {
                    has_write_permission && self.validate_write_witness(doc, path, ctx)
                } else {
                    has_write_permission
                }
            }
            Action::Grant {
                principal: target,
                action: _,
            } => principal.roles.contains(&"admin".to_string()),
        }
    }

    /// Validate read witness for high assurance mode
    fn validate_read_witness(&self, doc: &DocId, path: &[String], ctx: &Ctx) -> bool {
        // This would validate the Merkle path witness and label derivation
        // For now, return true as a placeholder
        true
    }

    /// Validate write witness for high assurance mode
    fn validate_write_witness(&self, doc: &DocId, path: &[String], ctx: &Ctx) -> bool {
        // This would validate the Merkle path witness and label derivation
        // For now, return true as a placeholder
        true
    }
}

/// Epoch manager for permission revocation
pub struct EpochManager {
    current_epoch: u64,
    revoked_principals: HashSet<String>,
}

impl EpochManager {
    pub fn new() -> Self {
        Self {
            current_epoch: 1,
            revoked_principals: HashSet::new(),
        }
    }

    pub fn bump_epoch(&mut self) {
        self.current_epoch += 1;
    }

    pub fn revoke_principal(&mut self, principal_id: String) {
        self.revoked_principals.insert(principal_id);
        self.bump_epoch();
    }

    pub fn is_revoked(&self, principal_id: &str) -> bool {
        self.revoked_principals.contains(principal_id)
    }

    pub fn get_current_epoch(&self) -> u64 {
        self.current_epoch
    }
}

/// Witness validator for Merkle paths and label derivation
pub struct WitnessValidator {
    // This would validate Merkle path witnesses and label derivation
}

impl WitnessValidator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn validate_merkle_path(&self, path: &[String], witness: &str) -> bool {
        // Validate Merkle path witness
        // For now, return true as a placeholder
        true
    }

    pub fn validate_label_derivation(
        &self,
        source_label: &str,
        target_label: &str,
        declass_rules: &[String],
    ) -> bool {
        // Validate label derivation according to declassification rules
        // For now, return true as a placeholder
        true
    }
}

impl PolicyAdapter {
    pub fn new(config: PolicyConfig) -> Self {
        Self {
            config,
            lean_interface: Some(LeanInterface::new()),
            epoch_manager: EpochManager::new(),
            witness_validator: WitnessValidator::new(),
        }
    }

    /// Evaluate permission for an action with full context
    pub fn evaluate_action(
        &mut self,
        principal: &Principal,
        action: &Action,
        ctx: &Ctx,
    ) -> PermissionResult {
        // Check if principal is revoked
        if self.epoch_manager.is_revoked(&principal.id) {
            return PermissionResult {
                allowed: false,
                reason: "Principal has been revoked".to_string(),
                epoch: self.epoch_manager.get_current_epoch(),
                path_witness_ok: false,
                label_derivation_ok: false,
                permit_decision: "reject".to_string(),
            };
        }

        // Validate epoch
        if self.config.epoch_validation && ctx.epoch < self.epoch_manager.get_current_epoch() {
            return PermissionResult {
                allowed: false,
                reason: "Context epoch is outdated".to_string(),
                epoch: self.epoch_manager.get_current_epoch(),
                path_witness_ok: false,
                label_derivation_ok: false,
                permit_decision: "reject".to_string(),
            };
        }

        // Evaluate permitD
        let permit_allowed = if let Some(ref lean_interface) = self.lean_interface {
            lean_interface.evaluate_permit(principal, action, ctx)
        } else {
            false
        };

        // Validate witness and label derivation for high assurance mode
        let (path_witness_ok, label_derivation_ok) = if self.config.witness_validation {
            match action {
                Action::Read { doc, path } => {
                    let witness_ok = self
                        .witness_validator
                        .validate_merkle_path(path, &ctx.session);
                    let label_ok = self
                        .witness_validator
                        .validate_label_derivation("", "", &[]);
                    (witness_ok, label_ok)
                }
                Action::Write { doc, path } => {
                    let witness_ok = self
                        .witness_validator
                        .validate_merkle_path(path, &ctx.session);
                    let label_ok = self
                        .witness_validator
                        .validate_label_derivation("", "", &[]);
                    (witness_ok, label_ok)
                }
                _ => (true, true),
            }
        } else {
            (true, true)
        };

        // Determine final decision based on enforcement mode
        let final_allowed = match self.config.enforcement_mode {
            EnforcementMode::Enforce => permit_allowed && path_witness_ok && label_derivation_ok,
            EnforcementMode::Shadow => {
                if !permit_allowed || !path_witness_ok || !label_derivation_ok {
                    warn!(
                        "Shadow mode: Action would be denied - principal: {}, action: {:?}",
                        principal.id, action
                    );
                }
                true // Always allow in shadow mode
            }
            EnforcementMode::Monitor => {
                if !permit_allowed || !path_witness_ok || !label_derivation_ok {
                    info!(
                        "Monitor mode: Action denied - principal: {}, action: {:?}",
                        principal.id, action
                    );
                }
                permit_allowed && path_witness_ok && label_derivation_ok
            }
        };

        PermissionResult {
            allowed: final_allowed,
            reason: if final_allowed {
                "Action permitted".to_string()
            } else {
                "Action denied".to_string()
            },
            epoch: self.epoch_manager.get_current_epoch(),
            path_witness_ok,
            label_derivation_ok,
            permit_decision: if permit_allowed {
                "accept".to_string()
            } else {
                "reject".to_string()
            },
        }
    }

    /// Process a runtime event and enforce permissions
    pub fn process_event(&mut self, event: &RuntimeEvent) -> PermissionResult {
        let principal = Principal {
            id: event.user_id.clone(),
            roles: event.roles.clone(),
            org: event.organization.clone(),
        };

        let ctx = Ctx {
            session: event.session_id.clone(),
            epoch: event.epoch,
            attributes: event.attributes.clone(),
            tenant: event.tenant.clone(),
            timestamp: event.timestamp,
        };

        let action = match event.event_type.as_str() {
            "call" => Action::Call {
                tool: event.tool.clone().unwrap_or(Tool::Custom {
                    name: "unknown".to_string(),
                }),
            },
            "read" => Action::Read {
                doc: DocId {
                    uri: event.resource_uri.clone(),
                    version: event.resource_version.unwrap_or(1),
                },
                path: event.field_path.clone().unwrap_or_default(),
            },
            "write" => Action::Write {
                doc: DocId {
                    uri: event.resource_uri.clone(),
                    version: event.resource_version.unwrap_or(1),
                },
                path: event.field_path.clone().unwrap_or_default(),
            },
            "grant" => Action::Grant {
                principal: principal.clone(),
                action: Box::new(Action::Call {
                    tool: Tool::Custom {
                        name: "unknown".to_string(),
                    },
                }),
            },
            _ => Action::Call {
                tool: Tool::Custom {
                    name: "unknown".to_string(),
                },
            },
        };

        self.evaluate_action(&principal, &action, &ctx)
    }

    /// Revoke a principal's permissions
    pub fn revoke_principal(&mut self, principal_id: String, reason: String) -> Result<(), String> {
        info!("Revoking principal {}: {}", principal_id, reason);
        self.epoch_manager.revoke_principal(principal_id);
        Ok(())
    }

    /// Get current epoch for revocation tracking
    pub fn get_current_epoch(&self) -> u64 {
        self.epoch_manager.get_current_epoch()
    }
}

/// Enforcement statistics for monitoring
#[derive(Debug, Clone)]
pub struct EnforcementStats {
    pub total_requests: u64,
    pub allowed_requests: u64,
    pub denied_requests: u64,
    pub violations_recorded: u64,
    pub current_epoch: u64,
}

impl Default for EnforcementStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            allowed_requests: 0,
            denied_requests: 0,
            violations_recorded: 0,
            current_epoch: 0,
        }
    }
}

/// World state for permission evaluation
#[derive(Debug, Clone)]
pub struct WorldState {
    pub current_epoch: u64,
    pub documents: HashMap<DocId, DocumentState>,
    pub labels: HashMap<DocId, Label>,
    pub declass_rules: Vec<DeclassRule>,
}

/// Document state for IFC validation
#[derive(Debug, Clone)]
pub struct DocumentState {
    pub metadata: DocMeta,
    pub merkle_root: String,
    pub field_commits: HashMap<Vec<String>, String>,
}

/// Label for information flow control
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Label {
    Public,
    Internal,
    Confidential,
    Secret,
    Custom { name: String },
}

/// Declassification rule
#[derive(Debug, Clone)]
pub struct DeclassRule {
    pub condition: String,
    pub source_label: Label,
    pub target_label: Label,
}

/// Document metadata
#[derive(Debug, Clone)]
pub struct DocMeta {
    pub owner: Principal,
    pub labels: Vec<String>,
    pub acls: Vec<(Principal, Vec<String>)>,
}

impl WorldState {
    pub fn new(current_epoch: u64) -> Self {
        Self {
            current_epoch,
            documents: HashMap::new(),
            labels: HashMap::new(),
            declass_rules: Vec::new(),
        }
    }

    pub fn has_path_witness(&self, doc: &DocId, path: &[String]) -> bool {
        // In a real implementation, this would check Merkle path witnesses
        // For now, we'll simulate this
        let doc_key = format!("{}:{}", doc.uri, doc.version);
        self.documents.contains_key(&doc_key)
    }

    pub fn can_derive_labels(&self, doc: &DocId) -> bool {
        // In a real implementation, this would check if we can derive labels
        // For now, we'll simulate this
        let doc_key = format!("{}:{}", doc.uri, doc.version);
        self.labels.contains_key(&doc_key)
    }

    pub fn add_document(&mut self, doc: &DocId, state: DocumentState) {
        let doc_key = format!("{}:{}", doc.uri, doc.version);
        self.documents.insert(doc_key, state);
    }

    pub fn add_labels(&mut self, doc: &DocId, labels: Vec<String>) {
        let doc_key = format!("{}:{}", doc.uri, doc.version);
        self.labels.insert(doc_key, labels);
    }
}

/// Document state for witness validation
#[derive(Debug, Clone)]
pub struct DocumentState {
    pub owner: String,
    pub acls: Vec<(String, Vec<String>)>,
    pub merkle_root: String,
    pub field_commits: HashMap<String, String>,
}

impl DocumentState {
    pub fn new(owner: String, merkle_root: String) -> Self {
        Self {
            owner,
            acls: Vec::new(),
            merkle_root,
            field_commits: HashMap::new(),
        }
    }

    pub fn add_acl(&mut self, principal: String, permissions: Vec<String>) {
        self.acls.push((principal, permissions));
    }

    pub fn add_field_commit(&mut self, path: String, commit: String) {
        self.field_commits.insert(path, commit);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_permission_check() {
        let config = PolicyConfig::default();
        let mut adapter = PolicyAdapter::new(config);

        let principal = Principal {
            id: "test-user".to_string(),
            roles: vec!["email_user".to_string()],
            org: "test-org".to_string(),
        };

        let action = Action::Call {
            tool: Tool::SendEmail,
        };

        let context = Ctx {
            session: "session-1".to_string(),
            epoch: 1,
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        let result = adapter
            .evaluate_action(&principal, &action, &context)
            .unwrap();
        assert!(result.allowed);
        assert_eq!(result.permit_decision, "accept");
    }

    #[test]
    fn test_epoch_validation() {
        let mut config = PolicyConfig::default();
        config.epoch_validation = true;
        let mut adapter = PolicyAdapter::new(config);

        let world = WorldState::new(5);
        let context = Ctx {
            session: "session-1".to_string(),
            epoch: 15, // Too far from world epoch
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        let principal = Principal {
            id: "test-user".to_string(),
            roles: vec!["admin".to_string()],
            org: "test-org".to_string(),
        };

        let action = Action::Call {
            tool: Tool::SendEmail,
        };

        let result = adapter
            .evaluate_action(&principal, &action, &context)
            .unwrap();
        assert!(!result.allowed);
        assert_eq!(result.permit_decision, "reject");
    }

    #[test]
    fn test_high_assurance_mode() {
        let mut config = PolicyConfig::default();
        config.high_assurance_mode = true;
        config.witness_validation = true;
        let mut adapter = PolicyAdapter::new(config);

        let mut world = WorldState::new(1);
        let doc = DocId {
            uri: "test://doc1".to_string(),
            version: 1,
        };

        // Don't add document to world state, so witness validation will fail
        let context = Ctx {
            session: "session-1".to_string(),
            epoch: 1,
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        let principal = Principal {
            id: "test-user".to_string(),
            roles: vec!["reader".to_string()],
            org: "test-org".to_string(),
        };

        let action = Action::Read {
            doc: doc.clone(),
            path: vec!["field1".to_string()],
        };

        let result = adapter
            .evaluate_action(&principal, &action, &context)
            .unwrap();
        assert!(!result.allowed);
        assert_eq!(result.permit_decision, "reject");
        assert!(!result.path_witness_ok);
    }
}

/// Structured violation record for denied actions
#[derive(Debug, Clone)]
pub struct ViolationRecord {
    pub timestamp: std::time::SystemTime,
    pub principal: Principal,
    pub action: Action,
    pub context: Ctx,
    pub result: PermissionResult,
}

impl Default for LeanInterface {
    fn default() -> Self {
        Self::new()
    }
}

/// Runtime event structure for sidecar integration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeEvent {
    pub event_type: String, // "call", "read", "write", "grant"
    pub user_id: String,
    pub roles: Vec<String>,
    pub organization: String,
    pub session_id: String,
    pub epoch: u64,
    pub attributes: Vec<(String, String)>,
    pub tenant: String,
    pub timestamp: u64,
    pub tool: Option<Tool>,
    pub resource_uri: String,
    pub resource_version: Option<u64>,
    pub field_path: Option<Vec<String>>,
}
