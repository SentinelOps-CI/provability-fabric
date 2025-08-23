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
        }
    }
}

/// File read response with security metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileReadResponse {
    pub content: Vec<u8>,
    pub file_size: u64,
    pub checksum: String,
    pub file_metadata: FileMetadata,
    pub read_time_ms: u64,
    pub security_metadata: SecurityMetadata,
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

/// File-read adapter with security enforcement
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

        Ok(())
    }

    /// Execute file read operation with security enforcement
    pub fn execute(&mut self, file_path: &str) -> Result<FileReadResponse, Box<dyn Error>> {
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
        };

        let mut adapter = FileReadAdapter::new(effect).unwrap();
        let result = adapter.execute(test_file.to_str().unwrap());

        assert!(result.is_ok());
        let response = result.unwrap();
        assert_eq!(response.content, b"Hello, World!");
        assert_eq!(response.file_size, 13);
        assert!(!response.checksum.is_empty());
    }
}
