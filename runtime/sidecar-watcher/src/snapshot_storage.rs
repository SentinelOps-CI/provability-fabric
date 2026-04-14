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
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use tokio::fs;
use tokio::sync::RwLock;

use super::cert_v1_core::CertV1Core;

/// Snapshot storage for decisions flagged by detectors or user annotations
pub struct SnapshotStorage {
    /// Storage directory
    storage_path: PathBuf,

    /// Snapshot metadata cache
    metadata_cache: Arc<RwLock<HashMap<String, SnapshotMetadata>>>,

    /// Maximum snapshots to keep per decision
    max_snapshots_per_decision: usize,
}

/// Snapshot metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotMetadata {
    /// Snapshot identifier
    pub snapshot_id: String,

    /// Decision identifier
    pub decision_id: String,

    /// Bundle identifier
    pub bundle_id: String,

    /// Session identifier
    pub session_id: String,

    /// Tenant identifier
    pub tenant_id: String,

    /// Snapshot type
    pub snapshot_type: SnapshotType,

    /// Creation timestamp
    pub created_at: u64,

    /// Snapshot size in bytes
    pub size_bytes: usize,

    /// File path
    pub file_path: String,

    /// Tags for categorization
    pub tags: Vec<String>,

    /// Flags that triggered this snapshot
    pub triggered_by: Vec<String>,
}

/// Snapshot type enumeration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SnapshotType {
    /// Detector flagged decision
    DetectorFlagged,
    /// User annotated decision
    UserAnnotated,
    /// Policy violation
    PolicyViolation,
    /// Performance anomaly
    PerformanceAnomaly,
    /// Security incident
    SecurityIncident,
    /// Manual snapshot
    Manual,
}

/// Decision snapshot data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionSnapshot {
    /// Snapshot metadata
    pub metadata: SnapshotMetadata,

    /// Core certificate
    pub core_cert: CertV1Core,

    /// Decision context
    pub context: DecisionContext,

    /// Prefix data
    pub prefix_data: PrefixData,

    /// Additional metadata
    pub additional_data: HashMap<String, serde_json::Value>,
}

/// Decision context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionContext {
    /// User making the decision
    pub user_id: String,

    /// Decision timestamp
    pub decision_timestamp: u64,

    /// Decision reason
    pub reason: String,

    /// Policy version
    pub policy_version: String,

    /// Environment information
    pub environment: HashMap<String, String>,

    /// Request metadata
    pub request_metadata: HashMap<String, String>,
}

/// Prefix data for replay
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PrefixData {
    /// Prefix identifier
    pub prefix_id: String,

    /// Prefix content
    pub content: String,

    /// Prefix hash
    pub hash: String,

    /// Prefix length
    pub length: usize,

    /// Prefix metadata
    pub metadata: HashMap<String, String>,
}

impl SnapshotStorage {
    /// Create a new snapshot storage instance
    pub fn new(storage_path: PathBuf) -> Self {
        Self {
            storage_path,
            metadata_cache: Arc::new(RwLock::new(HashMap::new())),
            max_snapshots_per_decision: 100,
        }
    }

    /// Store a decision snapshot
    #[allow(clippy::too_many_arguments)]
    pub async fn store_snapshot(
        &self,
        decision_id: &str,
        core_cert: CertV1Core,
        context: DecisionContext,
        prefix_data: PrefixData,
        snapshot_type: SnapshotType,
        triggered_by: Vec<String>,
        tags: Vec<String>,
    ) -> Result<String, String> {
        // Generate snapshot ID
        let snapshot_id = self.generate_snapshot_id(decision_id);

        // Create snapshot metadata
        let metadata = SnapshotMetadata {
            snapshot_id: snapshot_id.clone(),
            decision_id: decision_id.to_string(),
            bundle_id: core_cert.bundle_id.clone(),
            session_id: core_cert.session_id.clone(),
            tenant_id: core_cert.tenant_id.clone(),
            snapshot_type,
            created_at: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            size_bytes: 0,            // Will be updated after storage
            file_path: String::new(), // Will be set after file creation
            tags,
            triggered_by,
        };

        // Create decision snapshot
        let snapshot = DecisionSnapshot {
            metadata: metadata.clone(),
            core_cert,
            context,
            prefix_data,
            additional_data: HashMap::new(),
        };

        // Store snapshot to disk
        let file_path = self.store_snapshot_to_disk(&snapshot).await?;

        // Update metadata with file path and size
        let mut updated_metadata = metadata;
        updated_metadata.file_path = file_path.clone();
        updated_metadata.size_bytes = fs::metadata(&file_path)
            .await
            .map_err(|e| format!("Failed to get file metadata: {}", e))?
            .len() as usize;

        // Store metadata in cache
        {
            let mut cache = self.metadata_cache.write().await;
            cache.insert(snapshot_id.clone(), updated_metadata);
        }

        // Clean up old snapshots for this decision
        self.cleanup_old_snapshots(decision_id).await?;

        Ok(snapshot_id)
    }

    /// Retrieve a decision snapshot
    pub async fn get_snapshot(&self, snapshot_id: &str) -> Result<DecisionSnapshot, String> {
        // Get metadata from cache
        let metadata = {
            let cache = self.metadata_cache.read().await;
            cache.get(snapshot_id).cloned()
        };

        let metadata = metadata.ok_or_else(|| "Snapshot not found".to_string())?;

        // Load snapshot from disk
        self.load_snapshot_from_disk(&metadata.file_path).await
    }

    /// List snapshots for a decision
    pub async fn list_snapshots_for_decision(&self, decision_id: &str) -> Vec<SnapshotMetadata> {
        let cache = self.metadata_cache.read().await;
        cache
            .values()
            .filter(|metadata| metadata.decision_id == decision_id)
            .cloned()
            .collect()
    }

    /// Search snapshots by criteria
    pub async fn search_snapshots(
        &self,
        criteria: &SnapshotSearchCriteria,
    ) -> Vec<SnapshotMetadata> {
        let cache = self.metadata_cache.read().await;
        let mut results: Vec<SnapshotMetadata> = cache
            .values()
            .filter(|metadata| self.matches_criteria(metadata, criteria))
            .cloned()
            .collect();

        // Sort by creation time (newest first)
        results.sort_by(|a, b| b.created_at.cmp(&a.created_at));

        // Apply limit
        if let Some(limit) = criteria.limit {
            results.truncate(limit);
        }

        results
    }

    /// Delete a snapshot
    pub async fn delete_snapshot(&self, snapshot_id: &str) -> Result<(), String> {
        // Get metadata
        let metadata = {
            let cache = self.metadata_cache.read().await;
            cache.get(snapshot_id).cloned()
        };

        if let Some(metadata) = metadata {
            // Delete file from disk
            if let Err(e) = fs::remove_file(&metadata.file_path).await {
                eprintln!(
                    "Failed to delete snapshot file {}: {}",
                    metadata.file_path, e
                );
            }

            // Remove from cache
            {
                let mut cache = self.metadata_cache.write().await;
                cache.remove(snapshot_id);
            }
        }

        Ok(())
    }

    /// Get storage statistics
    pub async fn get_storage_stats(&self) -> StorageStats {
        let cache = self.metadata_cache.read().await;
        let total_snapshots = cache.len();
        let total_size: usize = cache.values().map(|m| m.size_bytes).sum();

        let mut snapshots_by_type: HashMap<String, usize> = HashMap::new();
        for metadata in cache.values() {
            let type_str = format!("{:?}", metadata.snapshot_type);
            *snapshots_by_type.entry(type_str).or_insert(0) += 1;
        }

        StorageStats {
            total_snapshots,
            total_size_bytes: total_size,
            snapshots_by_type,
        }
    }

    /// Generate snapshot ID
    fn generate_snapshot_id(&self, decision_id: &str) -> String {
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        format!("snapshot_{}_{}", decision_id, timestamp)
    }

    /// Store snapshot to disk
    async fn store_snapshot_to_disk(&self, snapshot: &DecisionSnapshot) -> Result<String, String> {
        // Create directory structure: snapshots/{tenant_id}/{decision_id}/
        let snapshot_dir = self
            .storage_path
            .join("snapshots")
            .join(&snapshot.metadata.tenant_id)
            .join(&snapshot.metadata.decision_id);

        fs::create_dir_all(&snapshot_dir)
            .await
            .map_err(|e| format!("Failed to create snapshot directory: {}", e))?;

        // Create file path
        let filename = format!("{}.json", snapshot.metadata.snapshot_id);
        let file_path = snapshot_dir.join(&filename);

        // Serialize and write snapshot
        let json = serde_json::to_string_pretty(snapshot)
            .map_err(|e| format!("Failed to serialize snapshot: {}", e))?;

        fs::write(&file_path, json)
            .await
            .map_err(|e| format!("Failed to write snapshot file: {}", e))?;

        Ok(file_path.to_string_lossy().to_string())
    }

    /// Load snapshot from disk
    async fn load_snapshot_from_disk(&self, file_path: &str) -> Result<DecisionSnapshot, String> {
        let content = fs::read_to_string(file_path)
            .await
            .map_err(|e| format!("Failed to read snapshot file: {}", e))?;

        let snapshot: DecisionSnapshot = serde_json::from_str(&content)
            .map_err(|e| format!("Failed to deserialize snapshot: {}", e))?;

        Ok(snapshot)
    }

    /// Clean up old snapshots for a decision
    async fn cleanup_old_snapshots(&self, decision_id: &str) -> Result<(), String> {
        let snapshots = self.list_snapshots_for_decision(decision_id).await;

        if snapshots.len() <= self.max_snapshots_per_decision {
            return Ok(());
        }

        // Sort by creation time (oldest first)
        let mut sorted_snapshots = snapshots;
        sorted_snapshots.sort_by(|a, b| a.created_at.cmp(&b.created_at));

        // Delete oldest snapshots
        let to_delete = sorted_snapshots.len() - self.max_snapshots_per_decision;
        for snapshot in sorted_snapshots.iter().take(to_delete) {
            self.delete_snapshot(&snapshot.snapshot_id).await?;
        }

        Ok(())
    }

    /// Check if snapshot matches search criteria
    fn matches_criteria(
        &self,
        metadata: &SnapshotMetadata,
        criteria: &SnapshotSearchCriteria,
    ) -> bool {
        if let Some(ref tenant_id) = criteria.tenant_id {
            if metadata.tenant_id != *tenant_id {
                return false;
            }
        }

        if let Some(ref bundle_id) = criteria.bundle_id {
            if metadata.bundle_id != *bundle_id {
                return false;
            }
        }

        if let Some(ref snapshot_type) = criteria.snapshot_type {
            if format!("{:?}", metadata.snapshot_type) != *snapshot_type {
                return false;
            }
        }

        if let Some(start_time) = criteria.start_time {
            if metadata.created_at < start_time {
                return false;
            }
        }

        if let Some(end_time) = criteria.end_time {
            if metadata.created_at > end_time {
                return false;
            }
        }

        if let Some(ref tags) = criteria.tags {
            for tag in tags {
                if !metadata.tags.contains(tag) {
                    return false;
                }
            }
        }

        true
    }
}

/// Snapshot search criteria
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SnapshotSearchCriteria {
    pub tenant_id: Option<String>,
    pub bundle_id: Option<String>,
    pub snapshot_type: Option<String>,
    pub start_time: Option<u64>,
    pub end_time: Option<u64>,
    pub tags: Option<Vec<String>>,
    pub limit: Option<usize>,
}

/// Storage statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageStats {
    pub total_snapshots: usize,
    pub total_size_bytes: usize,
    pub snapshots_by_type: HashMap<String, usize>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[tokio::test]
    async fn test_snapshot_storage() {
        let temp_dir = TempDir::new().unwrap();
        let storage = SnapshotStorage::new(temp_dir.path().to_path_buf());

        let core_cert = CertV1Core::new(
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

        let context = DecisionContext {
            user_id: "user-1".to_string(),
            decision_timestamp: 1234567890,
            reason: "Policy compliance".to_string(),
            policy_version: "1.0.0".to_string(),
            environment: HashMap::new(),
            request_metadata: HashMap::new(),
        };

        let prefix_data = PrefixData {
            prefix_id: "prefix-1".to_string(),
            content: "test content".to_string(),
            hash: "hash-123".to_string(),
            length: 12,
            metadata: HashMap::new(),
        };

        let snapshot_id = storage
            .store_snapshot(
                "decision-1",
                core_cert,
                context,
                prefix_data,
                SnapshotType::DetectorFlagged,
                vec!["pii_detection".to_string()],
                vec!["test".to_string()],
            )
            .await
            .unwrap();

        assert!(!snapshot_id.is_empty());

        let retrieved = storage.get_snapshot(&snapshot_id).await.unwrap();
        assert_eq!(retrieved.metadata.decision_id, "decision-1");
        assert_eq!(retrieved.core_cert.bundle_id, "bundle-123");
    }

    #[tokio::test]
    async fn test_snapshot_search() {
        let temp_dir = TempDir::new().unwrap();
        let storage = SnapshotStorage::new(temp_dir.path().to_path_buf());

        let core_cert = CertV1Core::new(
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

        let context = DecisionContext {
            user_id: "user-1".to_string(),
            decision_timestamp: 1234567890,
            reason: "Policy compliance".to_string(),
            policy_version: "1.0.0".to_string(),
            environment: HashMap::new(),
            request_metadata: HashMap::new(),
        };

        let prefix_data = PrefixData {
            prefix_id: "prefix-1".to_string(),
            content: "test content".to_string(),
            hash: "hash-123".to_string(),
            length: 12,
            metadata: HashMap::new(),
        };

        storage
            .store_snapshot(
                "decision-1",
                core_cert,
                context,
                prefix_data,
                SnapshotType::DetectorFlagged,
                vec!["pii_detection".to_string()],
                vec!["test".to_string()],
            )
            .await
            .unwrap();

        let criteria = SnapshotSearchCriteria {
            tenant_id: Some("tenant-1".to_string()),
            bundle_id: None,
            snapshot_type: None,
            start_time: None,
            end_time: None,
            tags: None,
            limit: Some(10),
        };

        let results = storage.search_snapshots(&criteria).await;
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].decision_id, "decision-1");
    }
}
