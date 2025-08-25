/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
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
use std::fs::{self, File, Metadata};
use std::io::{self, Read, Seek, SeekFrom};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

/// Resource mapping for file-read operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileReadResource {
    pub doc_id: String,          // Document ID (file path)
    pub field_path: Vec<String>, // Field path for structured data
    pub merkle_root: String,     // Merkle root for witness validation
    pub field_commit: String,    // Field commit hash
    pub label: String,           // Information flow control label
    pub content_type: String,    // Expected content type (json, text, binary)
}

/// Witness for file-read operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileReadWitness {
    pub merkle_path: Vec<String>,    // Merkle path from root to field
    pub sibling_hashes: Vec<String>, // Sibling hashes for path verification
    pub field_commit: String,        // Field commit hash
    pub timestamp: u64,              // Witness timestamp
    pub signature: String,           // Cryptographic signature
    pub file_hash: String,           // Hash of the entire file
}

/// Effect signature for file-read operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileReadEffect {
    pub allowed_paths: Vec<String>,
    pub max_file_size: usize,
    pub allowed_extensions: Vec<String>,
    pub read_only: bool,
    pub max_read_operations: u32,
    pub timeout_ms: u32,
    pub checksum_verification: bool,
    pub symlink_following: bool,
    pub resource_mapping: Option<FileReadResource>, // Optional resource mapping
    pub witness_required: bool,                     // Whether witness is required
    pub high_assurance_mode: bool,                  // High-assurance mode for IFC
}

impl Default for FileReadEffect {
    fn default() -> Self {
        Self {
            allowed_paths: vec!["/tmp".to_string(), "/var/log".to_string()],
            max_file_size: 100 * 1024 * 1024, // 100MB max
            allowed_extensions: vec!["txt".to_string(), "log".to_string(), "json".to_string()],
            read_only: true,
            max_read_operations: 1000,
            timeout_ms: 30000, // 30 second timeout
            checksum_verification: true,
            symlink_following: false, // Security: don't follow symlinks by default
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        }
    }
}

/// File read response with security metadata and witness validation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileReadResponse {
    pub content: Vec<u8>,
    pub file_size: u64,
    pub checksum: String,
    pub file_metadata: FileMetadata,
    pub read_time_ms: u64,
    pub security_metadata: SecurityMetadata,
    pub witness_validation: WitnessValidationResult,
    pub resource_access: ResourceAccessResult,
}

/// File metadata for audit and compliance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileMetadata {
    pub path: String,
    pub inode: u64,
    pub device: u64,
    pub permissions: u32,
    pub owner: u32,
    pub group: u32,
    pub created: Option<u64>,
    pub modified: Option<u64>,
    pub accessed: Option<u64>,
}

/// Security metadata for audit and compliance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityMetadata {
    pub path_resolved: String,
    pub symlink_count: u32,
    pub hardlink_count: u32,
    pub mount_point: Option<String>,
    pub filesystem_type: Option<String>,
    pub read_timestamp: u64,
    pub access_pattern: String,
}

/// Witness validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessValidationResult {
    pub valid: bool,
    pub merkle_path_verified: bool,
    pub field_commit_verified: bool,
    pub timestamp_valid: bool,
    pub signature_valid: bool,
    pub file_hash_verified: bool,
    pub error_message: Option<String>,
}

/// Resource access result for IFC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceAccessResult {
    pub access_granted: bool,
    pub label_derivation_ok: bool,
    pub declass_rule_applied: Option<String>,
    pub flow_violation: Option<String>,
    pub permitted_fields: Vec<String>,
    pub content_type_verified: bool,
}

/// File-read adapter with security enforcement and witness validation
pub struct FileReadAdapter {
    effect_signature: FileReadEffect,
    read_count: u32,
    last_read_time: Option<Instant>,
    read_history: HashMap<String, u32>,
}

impl FileReadAdapter {
    /// Create new file-read adapter with effect signature
    pub fn new(effect_signature: FileReadEffect) -> Result<Self, Box<dyn Error>> {
        // Validate effect signature
        Self::validate_effect_signature(&effect_signature)?;

        Ok(Self {
            effect_signature,
            read_count: 0,
            last_read_time: None,
            read_history: HashMap::new(),
        })
    }

    /// Validate effect signature for security compliance
    fn validate_effect_signature(effect: &FileReadEffect) -> Result<(), Box<dyn Error>> {
        // Validate allowed paths
        if effect.allowed_paths.is_empty() {
            return Err("No allowed paths specified".into());
        }

        // Validate file size limit
        if effect.max_file_size == 0 || effect.max_file_size > 1024 * 1024 * 1024 {
            // Max 1GB
            return Err("Invalid file size limit".into());
        }

        // Validate timeout
        if effect.timeout_ms == 0 || effect.timeout_ms > 300000 {
            // Max 5 minutes
            return Err("Invalid timeout value".into());
        }

        // Validate read operations limit
        if effect.max_read_operations == 0 || effect.max_read_operations > 10000 {
            return Err("Invalid read operations limit".into());
        }

        // Validate resource mapping if provided
        if let Some(ref resource) = effect.resource_mapping {
            if resource.doc_id.is_empty() || resource.merkle_root.is_empty() {
                return Err("Invalid resource mapping: missing doc_id or merkle_root".into());
            }
        }

        Ok(())
    }

    /// Execute file read operation with security enforcement and witness validation
    pub fn execute(
        &mut self,
        file_path: &str,
        witness: Option<&FileReadWitness>,
    ) -> Result<FileReadResponse, Box<dyn Error>> {
        let start_time = Instant::now();

        // Rate limiting check
        self.check_rate_limit()?;

        // Validate file path
        let path = Path::new(file_path);
        self.validate_file_path(path)?;

        // Check file size before reading
        let metadata = fs::metadata(path)?;
        if metadata.len() > self.effect_signature.max_file_size as u64 {
            return Err("File size exceeds limit".into());
        }

        // Read file content
        let mut file = File::open(path)?;
        let mut content = Vec::new();
        file.read_to_end(&mut content)?;

        // Verify checksum if enabled
        let checksum = if self.effect_signature.checksum_verification {
            self.calculate_checksum(&content)
        } else {
            "disabled".to_string()
        };

        // Extract file metadata
        let file_metadata = self.extract_file_metadata(path, &metadata)?;

        // Extract security metadata
        let security_metadata = self.extract_security_metadata(path)?;

        // Validate witness if required
        let witness_validation = if self.effect_signature.witness_required {
            self.validate_witness(witness, &content)?
        } else {
            WitnessValidationResult {
                valid: true,
                merkle_path_verified: true,
                field_commit_verified: true,
                timestamp_valid: true,
                signature_valid: true,
                file_hash_verified: true,
                error_message: None,
            }
        };

        // Validate resource access for IFC
        let resource_access = if let Some(ref resource) = self.effect_signature.resource_mapping {
            self.validate_resource_access(resource, &content, witness)?
        } else {
            ResourceAccessResult {
                access_granted: true,
                label_derivation_ok: true,
                declass_rule_applied: None,
                flow_violation: None,
                permitted_fields: vec![],
                content_type_verified: true,
            }
        };

        // Update adapter state
        self.read_count += 1;
        self.last_read_time = Some(Instant::now());
        self.read_history.insert(
            file_path.to_string(),
            self.read_history.get(file_path).unwrap_or(&0) + 1,
        );

        let read_time = start_time.elapsed();

        Ok(FileReadResponse {
            content,
            file_size: metadata.len(),
            checksum,
            file_metadata,
            read_time_ms: read_time.as_millis() as u64,
            security_metadata,
            witness_validation,
            resource_access,
        })
    }

    /// Validate file path against security constraints
    fn validate_file_path(&self, path: &Path) -> Result<(), Box<dyn Error>> {
        // Check if path is in allowed directories
        let mut current = path;
        let mut allowed = false;

        while let Some(parent) = current.parent() {
            if self
                .effect_signature
                .allowed_paths
                .iter()
                .any(|allowed_path| parent.starts_with(Path::new(allowed_path)))
            {
                allowed = true;
                break;
            }
            current = parent;
        }

        if !allowed {
            return Err("File path not in allowed directories".into());
        }

        // Check file extension if specified
        if !self.effect_signature.allowed_extensions.is_empty() {
            if let Some(extension) = path.extension() {
                let ext_str = extension.to_str().unwrap_or("");
                if !self
                    .effect_signature
                    .allowed_extensions
                    .contains(&ext_str.to_string())
                {
                    return Err("File extension not allowed".into());
                }
            }
        }

        // Check for symlinks if not allowed
        if !self.effect_signature.symlink_following {
            if path.is_symlink() {
                return Err("Symlink following not allowed".into());
            }
        }

        Ok(())
    }

    /// Validate witness for high-assurance mode
    fn validate_witness(
        &self,
        witness: Option<&FileReadWitness>,
        content: &[u8],
    ) -> Result<WitnessValidationResult, Box<dyn Error>> {
        let witness = witness.ok_or("Witness required but not provided")?;

        // Validate timestamp (within 5 minutes)
        let current_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs();
        let timestamp_valid = (current_time as i64 - witness.timestamp as i64).abs() < 300;

        // Validate field commit
        let content_hash = self.calculate_checksum(content);
        let field_commit_verified = content_hash == witness.field_commit;

        // Validate file hash
        let file_hash_verified = content_hash == witness.file_hash;

        // Validate Merkle path (simplified - would use actual Merkle tree verification)
        let merkle_path_verified = self.verify_merkle_path(witness)?;

        // Validate signature (simplified - would use actual cryptographic verification)
        let signature_valid = self.verify_signature(witness)?;

        let valid = timestamp_valid
            && field_commit_verified
            && merkle_path_verified
            && signature_valid
            && file_hash_verified;

        Ok(WitnessValidationResult {
            valid,
            merkle_path_verified,
            field_commit_verified,
            timestamp_valid,
            signature_valid,
            file_hash_verified,
            error_message: if valid {
                None
            } else {
                Some("Witness validation failed".to_string())
            },
        })
    }

    /// Validate resource access for information flow control
    fn validate_resource_access(
        &self,
        resource: &FileReadResource,
        content: &[u8],
        witness: Option<&FileReadWitness>,
    ) -> Result<ResourceAccessResult, Box<dyn Error>> {
        // Check if we have a valid witness in high-assurance mode
        let witness_ok = if self.effect_signature.high_assurance_mode {
            witness.is_some() && witness.as_ref().unwrap().field_commit == resource.field_commit
        } else {
            true
        };

        if !witness_ok {
            return Ok(ResourceAccessResult {
                access_granted: false,
                label_derivation_ok: false,
                declass_rule_applied: None,
                flow_violation: Some(
                    "Missing or invalid witness in high-assurance mode".to_string(),
                ),
                permitted_fields: vec![],
                content_type_verified: false,
            });
        }

        // Verify content type
        let content_type_verified = self.verify_content_type(content, &resource.content_type)?;

        // Extract permitted fields if content is structured
        let permitted_fields = if resource.content_type == "json" {
            self.extract_json_fields(content, &resource.field_path)?
        } else {
            vec!["content".to_string()] // For non-structured content
        };

        // Check label derivation (simplified IFC logic)
        let label_derivation_ok = self.can_derive_label(&resource.label)?;

        // Check for declassification rules
        let declass_rule_applied = self.check_declass_rules(&resource.label)?;

        Ok(ResourceAccessResult {
            access_granted: true,
            label_derivation_ok,
            declass_rule_applied,
            flow_violation: None,
            permitted_fields,
            content_type_verified,
        })
    }

    /// Verify content type matches expected type
    fn verify_content_type(
        &self,
        content: &[u8],
        expected_type: &str,
    ) -> Result<bool, Box<dyn Error>> {
        match expected_type {
            "json" => {
                // Try to parse as JSON
                serde_json::from_slice::<serde_json::Value>(content).is_ok()
            }
            "text" => {
                // Check if content is valid UTF-8 text
                String::from_utf8(content.to_vec()).is_ok()
            }
            "binary" => {
                // Binary content is always valid
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Extract fields from JSON content
    fn extract_json_fields(
        &self,
        content: &[u8],
        field_path: &[String],
    ) -> Result<Vec<String>, Box<dyn Error>> {
        let json_value: serde_json::Value = serde_json::from_slice(content)?;
        let mut permitted_fields = Vec::new();

        // Navigate to the specified field path
        let mut current = &json_value;
        for field in field_path {
            if let Some(value) = current.get(field) {
                current = value;
            } else {
                return Ok(permitted_fields); // Field not found
            }
        }

        // Extract field names at the target level
        if let Some(obj) = current.as_object() {
            for (key, _) in obj {
                permitted_fields.push(key.clone());
            }
        }

        Ok(permitted_fields)
    }

    /// Check if label can be derived (simplified IFC logic)
    fn can_derive_label(&self, label: &str) -> Result<bool, Box<dyn Error>> {
        // Simplified IFC logic - in practice, this would use the full IFC system
        match label {
            "public" => Ok(true),
            "internal" => Ok(true),
            "confidential" => Ok(false), // Would check declassification rules
            "secret" => Ok(false),       // Would check declassification rules
            _ => Ok(false),
        }
    }

    /// Check for applicable declassification rules
    fn check_declass_rules(&self, label: &str) -> Result<Option<String>, Box<dyn Error>> {
        // Simplified declassification logic
        match label {
            "confidential" => Ok(Some("confidential_to_internal".to_string())),
            "secret" => Ok(Some("secret_to_confidential".to_string())),
            _ => Ok(None),
        }
    }

    /// Verify Merkle path (simplified implementation)
    fn verify_merkle_path(&self, witness: &FileReadWitness) -> Result<bool, Box<dyn Error>> {
        // In a real implementation, this would verify the Merkle path from root to field
        // For now, we'll assume it's valid if the path is not empty
        Ok(!witness.merkle_path.is_empty())
    }

    /// Verify signature (simplified implementation)
    fn verify_signature(&self, witness: &FileReadWitness) -> Result<bool, Box<dyn Error>> {
        // In a real implementation, this would verify the cryptographic signature
        // For now, we'll assume it's valid if the signature is not empty
        Ok(!witness.signature.is_empty())
    }

    /// Extract comprehensive file metadata
    fn extract_file_metadata(
        &self,
        path: &Path,
        metadata: &Metadata,
    ) -> Result<FileMetadata, Box<dyn Error>> {
        Ok(FileMetadata {
            path: path.to_string_lossy().to_string(),
            inode: metadata.ino(),
            device: metadata.dev(),
            permissions: metadata.mode(),
            owner: metadata.uid(),
            group: metadata.gid(),
            created: metadata
                .created()
                .ok()
                .map(|t| t.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()),
            modified: metadata
                .modified()
                .ok()
                .map(|t| t.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()),
            accessed: metadata
                .accessed()
                .ok()
                .map(|t| t.duration_since(std::time::UNIX_EPOCH).unwrap().as_secs()),
        })
    }

    /// Extract security metadata
    fn extract_security_metadata(&self, path: &Path) -> Result<SecurityMetadata, Box<dyn Error>> {
        let mut symlink_count = 0;
        let mut current = path;

        // Count symlinks in path
        while let Some(parent) = current.parent() {
            if parent.is_symlink() {
                symlink_count += 1;
            }
            current = parent;
        }

        // Get hardlink count
        let hardlink_count = fs::metadata(path)?.nlink();

        Ok(SecurityMetadata {
            path_resolved: fs::canonicalize(path)?.to_string_lossy().to_string(),
            symlink_count,
            hardlink_count,
            mount_point: None,     // Would be determined from /proc/mounts
            filesystem_type: None, // Would be determined from /proc/mounts
            read_timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            access_pattern: "sequential".to_string(),
        })
    }

    /// Calculate SHA-256 checksum of file content
    fn calculate_checksum(&self, content: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(content);
        format!("{:x}", hasher.finalize())
    }

    /// Check rate limiting constraints
    fn check_rate_limit(&self) -> Result<(), Box<dyn Error>> {
        // Check total read operations
        if self.read_count >= self.effect_signature.max_read_operations {
            return Err("Maximum read operations exceeded".into());
        }

        // Check time-based rate limiting
        if let Some(last_time) = self.last_read_time {
            let elapsed = last_time.elapsed();
            if elapsed < Duration::from_millis(100) {
                // Max 10 reads per second
                return Err("Rate limit exceeded".into());
            }
        }

        Ok(())
    }

    /// Get adapter statistics
    pub fn get_stats(&self) -> HashMap<String, String> {
        let mut stats = HashMap::new();
        stats.insert("read_count".to_string(), self.read_count.to_string());
        stats.insert(
            "last_read_time".to_string(),
            self.last_read_time
                .map(|t| t.elapsed().as_secs().to_string())
                .unwrap_or_else(|| "never".to_string()),
        );
        stats.insert(
            "effect_signature".to_string(),
            format!("{:?}", self.effect_signature),
        );
        stats.insert(
            "read_history".to_string(),
            format!("{:?}", self.read_history),
        );
        stats.insert(
            "witness_required".to_string(),
            self.effect_signature.witness_required.to_string(),
        );
        stats.insert(
            "high_assurance_mode".to_string(),
            self.effect_signature.high_assurance_mode.to_string(),
        );
        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::write;
    use tempfile::tempdir;

    #[test]
    fn test_effect_signature_validation() {
        let valid_effect = FileReadEffect {
            allowed_paths: vec!["/tmp".to_string()],
            max_file_size: 1024 * 1024,
            allowed_extensions: vec!["txt".to_string()],
            read_only: true,
            max_read_operations: 100,
            timeout_ms: 30000,
            checksum_verification: true,
            symlink_following: false,
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };

        assert!(FileReadAdapter::validate_effect_signature(&valid_effect).is_ok());
    }

    #[test]
    fn test_invalid_path_rejected() {
        let effect = FileReadEffect {
            allowed_paths: vec!["/tmp".to_string()],
            max_file_size: 1024 * 1024,
            allowed_extensions: vec![],
            read_only: true,
            max_read_operations: 100,
            timeout_ms: 30000,
            checksum_verification: true,
            symlink_following: false,
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };

        let adapter = FileReadAdapter::new(effect).unwrap();
        let result = adapter.validate_file_path(Path::new("/etc/passwd"));
        assert!(result.is_err());
    }

    #[test]
    fn test_file_read_with_metadata() {
        let temp_dir = tempdir().unwrap();
        let test_file = temp_dir.path().join("test.txt");
        write(&test_file, "Hello, World!").unwrap();

        let effect = FileReadEffect {
            allowed_paths: vec![temp_dir.path().to_string_lossy().to_string()],
            max_file_size: 1024 * 1024,
            allowed_extensions: vec!["txt".to_string()],
            read_only: true,
            max_read_operations: 100,
            timeout_ms: 30000,
            checksum_verification: true,
            symlink_following: false,
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };

        let mut adapter = FileReadAdapter::new(effect).unwrap();
        let result = adapter.execute(test_file.to_str().unwrap(), None);

        assert!(result.is_ok());
        let response = result.unwrap();
        assert_eq!(response.content, b"Hello, World!");
        assert_eq!(response.file_size, 13);
        assert!(!response.checksum.is_empty());
    }

    #[test]
    fn test_resource_mapping_validation() {
        let valid_resource = FileReadResource {
            doc_id: "/tmp/data.json".to_string(),
            field_path: vec!["users".to_string()],
            merkle_root: "abc123".to_string(),
            field_commit: "def456".to_string(),
            label: "internal".to_string(),
            content_type: "json".to_string(),
        };

        let effect_with_resource = FileReadEffect {
            allowed_paths: vec!["/tmp".to_string()],
            max_file_size: 1024 * 1024,
            allowed_extensions: vec!["json".to_string()],
            read_only: true,
            max_read_operations: 100,
            timeout_ms: 30000,
            checksum_verification: true,
            symlink_following: false,
            resource_mapping: Some(valid_resource),
            witness_required: true,
            high_assurance_mode: true,
        };

        assert!(FileReadAdapter::validate_effect_signature(&effect_with_resource).is_ok());
    }

    #[test]
    fn test_invalid_resource_mapping_rejected() {
        let invalid_resource = FileReadResource {
            doc_id: "".to_string(), // Empty doc_id
            field_path: vec!["users".to_string()],
            merkle_root: "".to_string(), // Empty merkle_root
            field_commit: "def456".to_string(),
            label: "internal".to_string(),
            content_type: "json".to_string(),
        };

        let effect_with_invalid_resource = FileReadEffect {
            allowed_paths: vec!["/tmp".to_string()],
            max_file_size: 1024 * 1024,
            allowed_extensions: vec!["json".to_string()],
            read_only: true,
            max_read_operations: 100,
            timeout_ms: 30000,
            checksum_verification: true,
            symlink_following: false,
            resource_mapping: Some(invalid_resource),
            witness_required: true,
            high_assurance_mode: true,
        };

        assert!(FileReadAdapter::validate_effect_signature(&effect_with_invalid_resource).is_err());
    }
}
