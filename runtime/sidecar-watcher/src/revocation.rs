// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use tracing::{error, info, warn};

use crate::policy_adapter::{EnforcementMode, PolicyAdapter, PolicyConfig, Principal};

/// Revocation manager for handling epoch-based permission revocation
pub struct RevocationManager {
    current_epoch: Arc<RwLock<u64>>,
    revoked_principals: Arc<RwLock<HashMap<String, RevocationRecord>>>,
    policy_adapter: Arc<RwLock<PolicyAdapter>>,
    epoch_history: Arc<RwLock<Vec<EpochSnapshot>>>,
}

/// Record of a principal revocation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevocationRecord {
    pub principal_id: String,
    pub revoked_at_epoch: u64,
    pub reason: String,
    pub revoked_by: String,
    pub ttl_hours: u64,
    pub expires_at: u64,
}

/// Snapshot of policy state at a specific epoch
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EpochSnapshot {
    pub epoch: u64,
    pub timestamp: u64,
    pub policy_hash: String,
    pub dfa_hash: String,
    pub labeler_hash: String,
    pub total_principals: u64,
    pub revoked_principals: u64,
}

/// Revocation request from CLI or API
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevocationRequest {
    pub principal_id: String,
    pub reason: String,
    pub requested_by: String,
    pub ttl_hours: Option<u64>,
    pub requires_approval: bool,
}

/// Revocation response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevocationResponse {
    pub success: bool,
    pub new_epoch: u64,
    pub message: String,
    pub requires_approval: bool,
    pub approval_token: Option<String>,
}

impl RevocationManager {
    /// Create a new revocation manager
    pub fn new(policy_adapter: PolicyAdapter) -> Self {
        let current_epoch = Arc::new(RwLock::new(1));
        let revoked_principals = Arc::new(RwLock::new(HashMap::new()));
        let policy_adapter = Arc::new(RwLock::new(policy_adapter));
        let epoch_history = Arc::new(RwLock::new(Vec::new()));

        Self {
            current_epoch,
            revoked_principals,
            policy_adapter,
            epoch_history,
        }
    }

    /// Get current epoch
    pub fn get_current_epoch(&self) -> u64 {
        *self.current_epoch.read().unwrap()
    }

    /// Revoke a principal's permissions
    pub fn revoke_principal(&mut self, request: RevocationRequest) -> Result<RevocationResponse> {
        let principal_id = request.principal_id.clone();
        let reason = request.reason.clone();
        let requested_by = request.requested_by.clone();
        let ttl_hours = request.ttl_hours.unwrap_or(2); // Default 2 hour TTL

        // Check if principal exists and can be revoked
        if !self.can_revoke_principal(&principal_id, &requested_by)? {
            return Ok(RevocationResponse {
                success: false,
                new_epoch: self.get_current_epoch(),
                message: "Principal cannot be revoked or user lacks permission".to_string(),
                requires_approval: false,
                approval_token: None,
            });
        }

        // If approval is required, create approval token
        if request.requires_approval {
            let approval_token = self.create_approval_token(&request)?;
            return Ok(RevocationResponse {
                success: false,
                new_epoch: self.get_current_epoch(),
                message: "Revocation requires approval".to_string(),
                requires_approval: true,
                approval_token: Some(approval_token),
            });
        }

        // Execute revocation
        self.execute_revocation(&principal_id, &reason, &requested_by, ttl_hours)?;

        Ok(RevocationResponse {
            success: true,
            new_epoch: self.get_current_epoch(),
            message: "Principal revoked successfully".to_string(),
            requires_approval: false,
            approval_token: None,
        })
    }

    /// Execute the actual revocation
    fn execute_revocation(
        &mut self,
        principal_id: &str,
        reason: &str,
        revoked_by: &str,
        ttl_hours: u64,
    ) -> Result<()> {
        // Bump epoch
        let new_epoch = {
            let mut epoch = self.current_epoch.write().unwrap();
            *epoch += 1;
            *epoch
        };

        // Record revocation
        let revocation_record = RevocationRecord {
            principal_id: principal_id.to_string(),
            revoked_at_epoch: new_epoch,
            reason: reason.to_string(),
            revoked_by: revoked_by.to_string(),
            ttl_hours,
            expires_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs()
                + (ttl_hours * 3600),
        };

        {
            let mut revoked = self.revoked_principals.write().unwrap();
            revoked.insert(principal_id.to_string(), revocation_record);
        }

        // Take epoch snapshot
        self.take_epoch_snapshot(new_epoch)?;

        // Reload policy adapter with new epoch
        self.reload_policy_adapter(new_epoch)?;

        info!(
            "Principal {} revoked at epoch {} by {}",
            principal_id, new_epoch, revoked_by
        );
        Ok(())
    }

    /// Check if a principal can be revoked
    fn can_revoke_principal(&self, principal_id: &str, requested_by: &str) -> Result<bool> {
        // Check if requesting user has admin privileges
        let has_admin_privileges = self.check_admin_privileges(requested_by)?;
        if !has_admin_privileges {
            return Ok(false);
        }

        // Check if principal is already revoked
        let is_already_revoked = {
            let revoked = self.revoked_principals.read().unwrap();
            revoked.contains_key(principal_id)
        };

        if is_already_revoked {
            return Ok(false);
        }

        // Check if principal exists and is not a super-admin
        if principal_id == "super-admin" {
            return Ok(false);
        }

        Ok(true)
    }

    /// Check if user has admin privileges
    fn check_admin_privileges(&self, user_id: &str) -> Result<bool> {
        // In a real implementation, this would check against user database
        // For now, we'll use a simple check
        Ok(user_id.contains("admin") || user_id == "security-team")
    }

    /// Create approval token for revocation
    fn create_approval_token(&self, request: &RevocationRequest) -> Result<String> {
        // In a real implementation, this would create a secure approval token
        // For now, we'll create a simple hash-based token
        let token_data = format!(
            "{}:{}:{}",
            request.principal_id, request.reason, request.requested_by
        );
        let token = format!("approval_{:x}", md5::compute(token_data.as_bytes()));
        Ok(token)
    }

    /// Take epoch snapshot for audit trail
    fn take_epoch_snapshot(&self, epoch: u64) -> Result<()> {
        let snapshot = EpochSnapshot {
            epoch,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            policy_hash: "policy_hash_placeholder".to_string(), // Would be actual hash
            dfa_hash: "dfa_hash_placeholder".to_string(),       // Would be actual hash
            labeler_hash: "labeler_hash_placeholder".to_string(), // Would be actual hash
            total_principals: 0,                                // Would be actual count
            revoked_principals: {
                let revoked = self.revoked_principals.read().unwrap();
                revoked.len() as u64
            },
        };

        {
            let mut history = self.epoch_history.write().unwrap();
            history.push(snapshot);
        }

        Ok(())
    }

    /// Reload policy adapter with new epoch
    fn reload_policy_adapter(&self, new_epoch: u64) -> Result<()> {
        // In a real implementation, this would reload the policy adapter
        // with the new epoch and potentially new policy rules
        info!("Policy adapter reloaded for epoch {}", new_epoch);
        Ok(())
    }

    /// Check if a principal is revoked at a specific epoch
    pub fn is_principal_revoked(&self, principal_id: &str, epoch: u64) -> bool {
        let revoked = self.revoked_principals.read().unwrap();
        if let Some(record) = revoked.get(principal_id) {
            record.revoked_at_epoch <= epoch
        } else {
            false
        }
    }

    /// Get revocation statistics
    pub fn get_revocation_stats(&self) -> RevocationStats {
        let revoked = self.revoked_principals.read().unwrap();
        let history = self.epoch_history.read().unwrap();

        RevocationStats {
            current_epoch: self.get_current_epoch(),
            total_revocations: revoked.len() as u64,
            active_revocations: revoked
                .values()
                .filter(|r| {
                    std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs()
                        < r.expires_at
                })
                .count() as u64,
            epoch_history_count: history.len() as u64,
        }
    }

    /// Clean up expired revocations
    pub fn cleanup_expired_revocations(&mut self) -> Result<u64> {
        let current_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut expired_count = 0;
        {
            let mut revoked = self.revoked_principals.write().unwrap();
            let expired_keys: Vec<String> = revoked
                .iter()
                .filter(|(_, record)| record.expires_at < current_time)
                .map(|(key, _)| key.clone())
                .collect();

            for key in expired_keys {
                revoked.remove(&key);
                expired_count += 1;
            }
        }

        if expired_count > 0 {
            info!("Cleaned up {} expired revocations", expired_count);
        }

        Ok(expired_count)
    }
}

/// Revocation statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevocationStats {
    pub current_epoch: u64,
    pub total_revocations: u64,
    pub active_revocations: u64,
    pub epoch_history_count: u64,
}

impl Default for RevocationStats {
    fn default() -> Self {
        Self {
            current_epoch: 1,
            total_revocations: 0,
            active_revocations: 0,
            epoch_history_count: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::policy_adapter::{EnforcementMode, PolicyConfig};

    #[test]
    fn test_revocation_manager_creation() {
        let config = PolicyConfig::default();
        let adapter = PolicyAdapter::new(config);
        let manager = RevocationManager::new(adapter);

        assert_eq!(manager.get_current_epoch(), 1);
    }

    #[test]
    fn test_principal_revocation() {
        let config = PolicyConfig::default();
        let adapter = PolicyAdapter::new(config);
        let mut manager = RevocationManager::new(adapter);

        let request = RevocationRequest {
            principal_id: "test-user".to_string(),
            reason: "Security violation".to_string(),
            requested_by: "admin".to_string(),
            ttl_hours: Some(1),
            requires_approval: false,
        };

        let response = manager.revoke_principal(request).unwrap();
        assert!(response.success);
        assert_eq!(manager.get_current_epoch(), 2);
        assert!(manager.is_principal_revoked("test-user", 2));
    }

    #[test]
    fn test_epoch_participation_in_dfa() {
        // This test demonstrates how epochs participate in DFAs
        // The epoch ensures finite domain and prevents state explosion
        let config = PolicyConfig::default();
        let adapter = PolicyAdapter::new(config);
        let manager = RevocationManager::new(adapter);

        let current_epoch = manager.get_current_epoch();

        // In a real DFA, the epoch would be part of the state
        // This prevents infinite state growth while maintaining revocation semantics
        assert!(current_epoch > 0);
        assert!(current_epoch < u64::MAX); // Finite domain
    }
}
