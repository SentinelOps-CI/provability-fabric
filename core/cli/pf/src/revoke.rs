// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use clap::{Args, Subcommand};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use tracing::{error, info, warn};

/// Revocation management commands
#[derive(Subcommand)]
pub enum RevokeCommand {
    /// Revoke permissions for a principal
    Principal(PrincipalRevokeArgs),
    /// Revoke permissions for a role
    Role(RoleRevokeArgs),
    /// Revoke permissions for an organization
    Organization(OrganizationRevokeArgs),
    /// List current revocation status
    Status(StatusArgs),
    /// Rollback a revocation
    Rollback(RollbackArgs),
}

/// Arguments for revoking principal permissions
#[derive(Args)]
pub struct PrincipalRevokeArgs {
    /// Principal ID to revoke
    #[arg(long, short)]
    principal_id: String,

    /// Reason for revocation
    #[arg(long, short)]
    reason: String,

    /// Epoch to revoke from (defaults to current + 1)
    #[arg(long)]
    epoch: Option<u64>,

    /// Duration in seconds (defaults to 24 hours)
    #[arg(long, default_value = "86400")]
    duration_seconds: u64,

    /// Force revocation even if principal is active
    #[arg(long)]
    force: bool,

    /// Output file for revocation record
    #[arg(long)]
    output: Option<String>,
}

/// Arguments for revoking role permissions
#[derive(Args)]
pub struct RoleRevokeArgs {
    /// Role name to revoke
    #[arg(long, short)]
    role: String,

    /// Reason for revocation
    #[arg(long, short)]
    reason: String,

    /// Epoch to revoke from (defaults to current + 1)
    #[arg(long)]
    epoch: Option<u64>,

    /// Duration in seconds (defaults to 24 hours)
    #[arg(long, default_value = "86400")]
    duration_seconds: u64,

    /// Organizations to apply revocation to (defaults to all)
    #[arg(long)]
    organizations: Vec<String>,

    /// Output file for revocation record
    #[arg(long)]
    output: Option<String>,
}

/// Arguments for revoking organization permissions
#[derive(Args)]
pub struct OrganizationRevokeArgs {
    /// Organization name to revoke
    #[arg(long, short)]
    organization: String,

    /// Reason for revocation
    #[arg(long, short)]
    reason: String,

    /// Epoch to revoke from (defaults to current + 1)
    #[arg(long)]
    epoch: Option<u64>,

    /// Duration in seconds (defaults to 24 hours)
    #[arg(long, default_value = "86400")]
    duration_seconds: u64,

    /// Output file for revocation record
    #[arg(long)]
    output: Option<String>,
}

/// Arguments for checking revocation status
#[derive(Args)]
pub struct StatusArgs {
    /// Principal ID to check (optional)
    #[arg(long)]
    principal_id: Option<String>,

    /// Role to check (optional)
    #[arg(long)]
    role: Option<String>,

    /// Organization to check (optional)
    #[arg(long)]
    organization: Option<String>,

    /// Show active revocations only
    #[arg(long)]
    active_only: bool,

    /// Output format (json, yaml, table)
    #[arg(long, default_value = "table")]
    format: String,
}

/// Arguments for rolling back a revocation
#[derive(Args)]
pub struct RollbackArgs {
    /// Revocation ID to rollback
    #[arg(long, short)]
    revocation_id: String,

    /// Reason for rollback
    #[arg(long, short)]
    reason: String,

    /// Force rollback even if revocation is expired
    #[arg(long)]
    force: bool,

    /// Output file for rollback record
    #[arg(long)]
    output: Option<String>,
}

/// Revocation record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RevocationRecord {
    pub revocation_id: String,
    pub timestamp: u64,
    pub target_type: RevocationTarget,
    pub target_id: String,
    pub reason: String,
    pub epoch: u64,
    pub expires_at: u64,
    pub revoked_by: String,
    pub status: RevocationStatus,
    pub metadata: HashMap<String, String>,
}

/// Types of revocation targets
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RevocationTarget {
    Principal,
    Role,
    Organization,
}

/// Revocation status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RevocationStatus {
    Active,
    Expired,
    RolledBack,
}

/// Revocation manager
pub struct RevocationManager {
    revocations: HashMap<String, RevocationRecord>,
    current_epoch: u64,
    storage_path: String,
}

impl RevocationManager {
    /// Create a new revocation manager
    pub fn new(storage_path: String) -> Result<Self> {
        let mut manager = Self {
            revocations: HashMap::new(),
            current_epoch: 1,
            storage_path,
        };

        // Load existing revocations
        manager.load_revocations()?;

        Ok(manager)
    }

    /// Execute revocation command
    pub fn execute(&mut self, command: RevokeCommand) -> Result<()> {
        match command {
            RevokeCommand::Principal(args) => self.revoke_principal(args),
            RevokeCommand::Role(args) => self.revoke_role(args),
            RevokeCommand::Organization(args) => self.revoke_organization(args),
            RevokeCommand::Status(args) => self.show_status(args),
            RevokeCommand::Rollback(args) => self.rollback_revocation(args),
        }
    }

    /// Revoke permissions for a principal
    fn revoke_principal(&mut self, args: PrincipalRevokeArgs) -> Result<()> {
        let epoch = args.epoch.unwrap_or(self.current_epoch + 1);
        let expires_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() + args.duration_seconds;

        let revocation = RevocationRecord {
            revocation_id: self.generate_revocation_id(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            target_type: RevocationTarget::Principal,
            target_id: args.principal_id.clone(),
            reason: args.reason.clone(),
            epoch,
            expires_at,
            revoked_by: "cli-user".to_string(), // TODO: Get from auth context
            status: RevocationStatus::Active,
            metadata: HashMap::new(),
        };

        // Check if principal is already revoked
        if let Some(existing) = self.revocations.values().find(|r| {
            r.target_type == RevocationTarget::Principal
                && r.target_id == args.principal_id
                && r.status == RevocationStatus::Active
        }) {
            if !args.force {
                return Err(anyhow::anyhow!(
                    "Principal {} is already revoked (ID: {})",
                    args.principal_id,
                    existing.revocation_id
                ));
            }
            warn!("Principal {} is already revoked, forcing new revocation", args.principal_id);
        }

        self.revocations.insert(revocation.revocation_id.clone(), revocation.clone());
        self.save_revocations()?;

        info!(
            "Revoked principal {} at epoch {} (expires: {})",
            args.principal_id, epoch, expires_at
        );

        // Output revocation record if requested
        if let Some(output_path) = args.output {
            self.output_revocation_record(&revocation, &output_path)?;
        }

        Ok(())
    }

    /// Revoke permissions for a role
    fn revoke_role(&mut self, args: RoleRevokeArgs) -> Result<()> {
        let epoch = args.epoch.unwrap_or(self.current_epoch + 1);
        let expires_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() + args.duration_seconds;

        let revocation = RevocationRecord {
            revocation_id: self.generate_revocation_id(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            target_type: RevocationTarget::Role,
            target_id: args.role.clone(),
            reason: args.reason.clone(),
            epoch,
            expires_at,
            revoked_by: "cli-user".to_string(),
            status: RevocationStatus::Active,
            metadata: {
                let mut meta = HashMap::new();
                if !args.organizations.is_empty() {
                    meta.insert("organizations".to_string(), args.organizations.join(","));
                }
                meta
            },
        };

        self.revocations.insert(revocation.revocation_id.clone(), revocation.clone());
        self.save_revocations()?;

        info!(
            "Revoked role {} at epoch {} (expires: {})",
            args.role, epoch, expires_at
        );

        if let Some(output_path) = args.output {
            self.output_revocation_record(&revocation, &output_path)?;
        }

        Ok(())
    }

    /// Revoke permissions for an organization
    fn revoke_organization(&mut self, args: OrganizationRevokeArgs) -> Result<()> {
        let epoch = args.epoch.unwrap_or(self.current_epoch + 1);
        let expires_at = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() + args.duration_seconds;

        let revocation = RevocationRecord {
            revocation_id: self.generate_revocation_id(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            target_type: RevocationTarget::Organization,
            target_id: args.organization.clone(),
            reason: args.reason.clone(),
            epoch,
            expires_at,
            revoked_by: "cli-user".to_string(),
            status: RevocationStatus::Active,
            metadata: HashMap::new(),
        };

        self.revocations.insert(revocation.revocation_id.clone(), revocation.clone());
        self.save_revocations()?;

        info!(
            "Revoked organization {} at epoch {} (expires: {})",
            args.organization, epoch, expires_at
        );

        if let Some(output_path) = args.output {
            self.output_revocation_record(&revocation, &output_path)?;
        }

        Ok(())
    }

    /// Show revocation status
    fn show_status(&self, args: StatusArgs) -> Result<()> {
        let mut filtered_revocations: Vec<&RevocationRecord> = self.revocations.values().collect();

        // Apply filters
        if let Some(principal_id) = &args.principal_id {
            filtered_revocations.retain(|r| {
                r.target_type == RevocationTarget::Principal && r.target_id == *principal_id
            });
        }

        if let Some(role) = &args.role {
            filtered_revocations.retain(|r| {
                r.target_type == RevocationTarget::Role && r.target_id == *role
            });
        }

        if let Some(organization) = &args.organization {
            filtered_revocations.retain(|r| {
                r.target_type == RevocationTarget::Organization && r.target_id == *organization
            });
        }

        if args.active_only {
            filtered_revocations.retain(|r| r.status == RevocationStatus::Active);
        }

        // Sort by timestamp (newest first)
        filtered_revocations.sort_by(|a, b| b.timestamp.cmp(&a.timestamp));

        match args.format.as_str() {
            "json" => {
                let json = serde_json::to_string_pretty(&filtered_revocations)?;
                println!("{}", json);
            }
            "yaml" => {
                let yaml = serde_yaml::to_string(&filtered_revocations)?;
                println!("{}", yaml);
            }
            "table" => {
                self.print_status_table(&filtered_revocations);
            }
            _ => {
                return Err(anyhow::anyhow!("Unsupported format: {}", args.format));
            }
        }

        Ok(())
    }

    /// Rollback a revocation
    fn rollback_revocation(&mut self, args: RollbackArgs) -> Result<()> {
        let revocation = self
            .revocations
            .get_mut(&args.revocation_id)
            .ok_or_else(|| anyhow::anyhow!("Revocation {} not found", args.revocation_id))?;

        if revocation.status == RevocationStatus::Expired && !args.force {
            return Err(anyhow::anyhow!(
                "Revocation {} is expired. Use --force to rollback anyway.",
                args.revocation_id
            ));
        }

        let old_status = revocation.status.clone();
        revocation.status = RevocationStatus::RolledBack;
        revocation.metadata.insert("rollback_reason".to_string(), args.reason.clone());
        revocation.metadata.insert(
            "rollback_timestamp".to_string(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs()
                .to_string(),
        );

        self.save_revocations()?;

        info!(
            "Rolled back revocation {} (status: {} -> RolledBack)",
            args.revocation_id, old_status
        );

        if let Some(output_path) = args.output {
            self.output_revocation_record(revocation, &output_path)?;
        }

        Ok(())
    }

    /// Generate a unique revocation ID
    fn generate_revocation_id(&self) -> String {
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        format!("rev_{:x}", timestamp)
    }

    /// Load revocations from storage
    fn load_revocations(&mut self) -> Result<()> {
        let path = Path::new(&self.storage_path);
        if path.exists() {
            let content = fs::read_to_string(path)
                .context("Failed to read revocation storage file")?;
            let revocations: HashMap<String, RevocationRecord> = serde_json::from_str(&content)
                .context("Failed to parse revocation storage file")?;
            self.revocations = revocations;
        }
        Ok(())
    }

    /// Save revocations to storage
    fn save_revocations(&self) -> Result<()> {
        let path = Path::new(&self.storage_path);
        let content = serde_json::to_string_pretty(&self.revocations)
            .context("Failed to serialize revocations")?;
        fs::write(path, content).context("Failed to write revocation storage file")?;
        Ok(())
    }

    /// Output revocation record to file
    fn output_revocation_record(&self, record: &RevocationRecord, path: &str) -> Result<()> {
        let content = serde_json::to_string_pretty(record)
            .context("Failed to serialize revocation record")?;
        fs::write(path, content).context("Failed to write revocation record file")?;
        Ok(())
    }

    /// Print status table
    fn print_status_table(&self, revocations: &[&RevocationRecord]) {
        println!("Revocation Status");
        println!("=================");
        println!(
            "{:<20} {:<15} {:<20} {:<10} {:<15} {:<10}",
            "ID", "Type", "Target", "Epoch", "Status", "Expires"
        );
        println!("{:-<100}", "");

        for revocation in revocations {
            let expires_str = if revocation.expires_at == 0 {
                "Never".to_string()
            } else {
                let expires = std::time::UNIX_EPOCH + std::time::Duration::from_secs(revocation.expires_at);
                format!("{:?}", expires)
            };

            println!(
                "{:<20} {:<15} {:<20} {:<10} {:<15} {:<10}",
                &revocation.revocation_id[..20.min(revocation.revocation_id.len())],
                format!("{:?}", revocation.target_type),
                &revocation.target_id[..20.min(revocation.target_id.len())],
                revocation.epoch,
                format!("{:?}", revocation.status),
                expires_str
            );
        }
        println!();
    }

    /// Get current epoch
    pub fn current_epoch(&self) -> u64 {
        self.current_epoch
    }

    /// Check if a principal is revoked
    pub fn is_principal_revoked(&self, principal_id: &str, current_epoch: u64) -> bool {
        self.revocations.values().any(|r| {
            r.target_type == RevocationTarget::Principal
                && r.target_id == principal_id
                && r.status == RevocationStatus::Active
                && current_epoch >= r.epoch
                && (r.expires_at == 0 || current_epoch < r.expires_at)
        })
    }

    /// Check if a role is revoked
    pub fn is_role_revoked(&self, role: &str, current_epoch: u64) -> bool {
        self.revocations.values().any(|r| {
            r.target_type == RevocationTarget::Role
                && r.target_id == role
                && r.status == RevocationStatus::Active
                && current_epoch >= r.epoch
                && (r.expires_at == 0 || current_epoch < r.expires_at)
        })
    }

    /// Check if an organization is revoked
    pub fn is_organization_revoked(&self, organization: &str, current_epoch: u64) -> bool {
        self.revocations.values().any(|r| {
            r.target_type == RevocationTarget::Organization
                && r.target_id == organization
                && r.status == RevocationStatus::Active
                && current_epoch >= r.epoch
                && (r.expires_at == 0 || current_epoch < r.expires_at)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_revocation_manager_creation() {
        let temp_dir = tempdir().unwrap();
        let storage_path = temp_dir.path().join("revocations.json").to_string_lossy().to_string();
        
        let manager = RevocationManager::new(storage_path).unwrap();
        assert_eq!(manager.current_epoch(), 1);
        assert_eq!(manager.revocations.len(), 0);
    }

    #[test]
    fn test_principal_revocation() {
        let temp_dir = tempdir().unwrap();
        let storage_path = temp_dir.path().join("revocations.json").to_string_lossy().to_string();
        
        let mut manager = RevocationManager::new(storage_path).unwrap();
        
        let args = PrincipalRevokeArgs {
            principal_id: "test-user".to_string(),
            reason: "Security violation".to_string(),
            epoch: None,
            duration_seconds: 3600,
            force: false,
            output: None,
        };

        manager.revoke_principal(args).unwrap();
        
        assert_eq!(manager.revocations.len(), 1);
        assert!(manager.is_principal_revoked("test-user", 2));
        assert!(!manager.is_principal_revoked("test-user", 1));
    }

    #[test]
    fn test_role_revocation() {
        let temp_dir = tempdir().unwrap();
        let storage_path = temp_dir.path().join("revocations.json").to_string_lossy().to_string();
        
        let mut manager = RevocationManager::new(storage_path).unwrap();
        
        let args = RoleRevokeArgs {
            role: "admin".to_string(),
            reason: "Role abuse".to_string(),
            epoch: None,
            duration_seconds: 7200,
            organizations: vec!["org1".to_string()],
            output: None,
        };

        manager.revoke_role(args).unwrap();
        
        assert_eq!(manager.revocations.len(), 1);
        assert!(manager.is_role_revoked("admin", 2));
        assert!(!manager.is_role_revoked("admin", 1));
    }

    #[test]
    fn test_organization_revocation() {
        let temp_dir = tempdir().unwrap();
        let storage_path = temp_dir.path().join("revocations.json").to_string_lossy().to_string();
        
        let mut manager = RevocationManager::new(storage_path).unwrap();
        
        let args = OrganizationRevokeArgs {
            organization: "malicious-org".to_string(),
            reason: "Compliance violation".to_string(),
            epoch: None,
            duration_seconds: 86400,
            output: None,
        };

        manager.revoke_organization(args).unwrap();
        
        assert_eq!(manager.revocations.len(), 1);
        assert!(manager.is_organization_revoked("malicious-org", 2));
        assert!(!manager.is_organization_revoked("malicious-org", 1));
    }
}
