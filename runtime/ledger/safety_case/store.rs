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

use super::builder::{SafetyCaseBundle, SafetyCaseStore as BaseStore};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use uuid::Uuid;

/// Safety case store configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StoreConfig {
    pub base_directory: PathBuf,
    pub retention_days: u32,
    pub max_bundles_per_session: usize,
    pub enable_compression: bool,
    pub enable_encryption: bool,
    pub encryption_key: Option<String>,
    pub backup_enabled: bool,
    pub backup_directory: Option<PathBuf>,
    pub backup_retention_days: u32,
}

impl Default for StoreConfig {
    fn default() -> Self {
        Self {
            base_directory: PathBuf::from("./safety_cases"),
            retention_days: 90,
            max_bundles_per_session: 1000,
            enable_compression: false,
            enable_encryption: false,
            encryption_key: None,
            backup_enabled: false,
            backup_directory: None,
            backup_retention_days: 365,
        }
    }
}

/// Safety case index entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BundleIndexEntry {
    pub session_id: String,
    pub bundle_id: String,
    pub created_at: u64,
    pub expires_at: u64,
    pub file_path: PathBuf,
    pub file_size: u64,
    pub checksum: String,
    pub tags: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// Safety case store with advanced features
pub struct SafetyCaseStore {
    config: StoreConfig,
    base_store: BaseStore,
    index: RwLock<HashMap<String, Vec<BundleIndexEntry>>>,
    index_file: PathBuf,
}

impl SafetyCaseStore {
    /// Create new safety case store
    pub fn new(config: StoreConfig) -> Result<Self, String> {
        // Create base directory if it doesn't exist
        fs::create_dir_all(&config.base_directory)
            .map_err(|e| format!("Failed to create base directory: {}", e))?;
        
        let base_store = BaseStore::new(config.base_directory.clone())
            .with_retention(config.retention_days);
        
        let index_file = config.base_directory.join("bundle_index.json");
        
        let store = Self {
            config,
            base_store,
            index: RwLock::new(HashMap::new()),
            index_file,
        };
        
        // Load existing index
        store.load_index()?;
        
        Ok(store)
    }

    /// Store safety case bundle with indexing
    pub async fn store_bundle(&self, bundle: &SafetyCaseBundle) -> Result<PathBuf, String> {
        // Store the bundle using base store
        let stored_path = self.base_store.store_bundle(bundle)?;
        
        // Create index entry
        let entry = BundleIndexEntry {
            session_id: bundle.metadata.session_id.clone(),
            bundle_id: bundle.metadata.bundle_id.clone(),
            created_at: bundle.metadata.created_at,
            expires_at: bundle.metadata.expires_at,
            file_path: stored_path.clone(),
            file_size: bundle.metadata.total_size_bytes,
            checksum: bundle.metadata.checksum.clone(),
            tags: self.extract_tags(bundle),
            metadata: self.extract_metadata(bundle),
        };
        
        // Add to index
        {
            let mut index = self.index.write().await;
            let session_bundles = index
                .entry(bundle.metadata.session_id.clone())
                .or_insert_with(Vec::new);
            
            // Check max bundles per session
            if session_bundles.len() >= self.config.max_bundles_per_session {
                // Remove oldest bundle
                session_bundles.sort_by_key(|e| e.created_at);
                if let Some(oldest) = session_bundles.first() {
                    let _ = fs::remove_file(&oldest.file_path);
                    session_bundles.remove(0);
                }
            }
            
            session_bundles.push(entry);
        }
        
        // Save index
        self.save_index().await?;
        
        // Create backup if enabled
        if self.config.backup_enabled {
            self.create_backup(&stored_path).await?;
        }
        
        Ok(stored_path)
    }

    /// Retrieve safety case bundle by session and bundle ID
    pub async fn retrieve_bundle(&self, session_id: &str, bundle_id: &str) -> Result<SafetyCaseBundle, String> {
        // Check index first
        {
            let index = self.index.read().await;
            if let Some(session_bundles) = index.get(session_id) {
                if let Some(entry) = session_bundles.iter().find(|e| e.bundle_id == bundle_id) {
                    // Verify file still exists and checksum matches
                    if entry.file_path.exists() {
                        let content = fs::read_to_string(&entry.file_path)
                            .map_err(|e| format!("Failed to read bundle file: {}", e))?;
                        
                        let bundle: SafetyCaseBundle = serde_json::from_str(&content)
                            .map_err(|e| format!("Failed to parse bundle JSON: {}", e))?;
                        
                        // Verify checksum
                        if bundle.metadata.checksum == entry.checksum {
                            return Ok(bundle);
                        } else {
                            return Err("Bundle checksum mismatch".to_string());
                        }
                    }
                }
            }
        }
        
        // Fallback to base store
        self.base_store.retrieve_bundle(session_id, bundle_id)
    }

    /// Search bundles by criteria
    pub async fn search_bundles(&self, criteria: &SearchCriteria) -> Result<Vec<BundleIndexEntry>, String> {
        let index = self.index.read().await;
        let mut results = Vec::new();
        
        for (session_id, session_bundles) in index.iter() {
            for entry in session_bundles {
                if self.matches_criteria(entry, criteria) {
                    results.push(entry.clone());
                }
            }
        }
        
        // Sort results
        match criteria.sort_by.as_deref() {
            Some("created_at") => results.sort_by_key(|e| e.created_at),
            Some("expires_at") => results.sort_by_key(|e| e.expires_at),
            Some("file_size") => results.sort_by_key(|e| e.file_size),
            _ => results.sort_by_key(|e| e.created_at),
        }
        
        // Apply limit
        if let Some(limit) = criteria.limit {
            results.truncate(limit);
        }
        
        Ok(results)
    }

    /// List all sessions
    pub async fn list_sessions(&self) -> Result<Vec<String>, String> {
        let index = self.index.read().await;
        Ok(index.keys().cloned().collect())
    }

    /// List bundles for a session
    pub async fn list_session_bundles(&self, session_id: &str) -> Result<Vec<BundleIndexEntry>, String> {
        let index = self.index.read().await;
        Ok(index.get(session_id).cloned().unwrap_or_default())
    }

    /// Get bundle statistics
    pub async fn get_statistics(&self) -> Result<StoreStatistics, String> {
        let index = self.index.read().await;
        let mut stats = StoreStatistics::default();
        
        for (session_id, session_bundles) in index.iter() {
            stats.total_sessions += 1;
            stats.total_bundles += session_bundles.len() as u64;
            
            for entry in session_bundles {
                stats.total_size_bytes += entry.file_size;
                stats.oldest_bundle = stats.oldest_bundle.min(entry.created_at);
                stats.newest_bundle = stats.newest_bundle.max(entry.created_at);
            }
        }
        
        Ok(stats)
    }

    /// Clean up expired bundles
    pub async fn cleanup_expired(&self) -> Result<CleanupResult, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut result = CleanupResult::default();
        let mut index = self.index.write().await;
        
        for (session_id, session_bundles) in index.iter_mut() {
            let mut to_remove = Vec::new();
            
            for (i, entry) in session_bundles.iter().enumerate() {
                if entry.expires_at <= now {
                    to_remove.push(i);
                    result.bundles_removed += 1;
                    result.size_freed_bytes += entry.file_size;
                    
                    // Remove file
                    if let Err(e) = fs::remove_file(&entry.file_path) {
                        result.errors.push(format!("Failed to remove expired bundle {}: {}", entry.file_path.display(), e));
                    }
                }
            }
            
            // Remove expired entries (in reverse order to maintain indices)
            for &i in to_remove.iter().rev() {
                session_bundles.remove(i);
            }
            
            // Remove empty sessions
            if session_bundles.is_empty() {
                result.sessions_removed += 1;
            }
        }
        
        // Remove empty sessions from index
        index.retain(|_, bundles| !bundles.is_empty());
        
        // Save updated index
        drop(index);
        self.save_index().await?;
        
        // Clean up base store
        let base_cleaned = self.base_store.cleanup_all_expired()?;
        result.bundles_removed += base_cleaned as u64;
        
        Ok(result)
    }

    /// Export bundle to different formats
    pub async fn export_bundle(&self, session_id: &str, bundle_id: &str, format: ExportFormat) -> Result<Vec<u8>, String> {
        let bundle = self.retrieve_bundle(session_id, bundle_id).await?;
        
        match format {
            ExportFormat::Json => {
                serde_json::to_vec_pretty(&bundle)
                    .map_err(|e| format!("Failed to serialize bundle to JSON: {}", e))
            }
            ExportFormat::Yaml => {
                serde_yaml::to_vec(&bundle)
                    .map_err(|e| format!("Failed to serialize bundle to YAML: {}", e))
            }
            ExportFormat::Zip => {
                let temp_dir = tempfile::tempdir()
                    .map_err(|e| format!("Failed to create temp directory: {}", e))?;
                
                let builder = super::builder::SafetyCaseBuilder::new(
                    session_id.to_string(),
                    bundle_id.to_string(),
                    temp_dir.path().to_path_buf(),
                );
                
                let zip_path = builder.create_zip_archive(&bundle)?;
                let zip_data = fs::read(&zip_path)
                    .map_err(|e| format!("Failed to read ZIP file: {}", e))?;
                
                Ok(zip_data)
            }
        }
    }

    /// Import bundle from different formats
    pub async fn import_bundle(&self, data: &[u8], format: ExportFormat) -> Result<PathBuf, String> {
        let bundle: SafetyCaseBundle = match format {
            ExportFormat::Json => {
                serde_json::from_slice(data)
                    .map_err(|e| format!("Failed to parse JSON bundle: {}", e))?
            }
            ExportFormat::Yaml => {
                serde_yaml::from_slice(data)
                    .map_err(|e| format!("Failed to parse YAML bundle: {}", e))?
            }
            ExportFormat::Zip => {
                return Err("Import from ZIP not supported".to_string());
            }
        };
        
        self.store_bundle(&bundle).await
    }

    /// Load index from file
    fn load_index(&self) -> Result<(), String> {
        if !self.index_file.exists() {
            return Ok(());
        }
        
        let content = fs::read_to_string(&self.index_file)
            .map_err(|e| format!("Failed to read index file: {}", e))?;
        
        let index: HashMap<String, Vec<BundleIndexEntry>> = serde_json::from_str(&content)
            .map_err(|e| format!("Failed to parse index JSON: {}", e))?;
        
        // Spawn async task to update the index
        let index_file = self.index_file.clone();
        tokio::spawn(async move {
            let _ = Self::update_index_from_filesystem(&index_file, index).await;
        });
        
        Ok(())
    }

    /// Save index to file
    async fn save_index(&self) -> Result<(), String> {
        let index = self.index.read().await;
        let content = serde_json::to_string_pretty(&*index)
            .map_err(|e| format!("Failed to serialize index: {}", e))?;
        
        // Write to temporary file first
        let temp_file = self.index_file.with_extension("tmp");
        fs::write(&temp_file, content)
            .map_err(|e| format!("Failed to write temp index file: {}", e))?;
        
        // Atomic rename
        fs::rename(&temp_file, &self.index_file)
            .map_err(|e| format!("Failed to rename temp index file: {}", e))?;
        
        Ok(())
    }

    /// Update index from filesystem
    async fn update_index_from_filesystem(
        index_file: &Path,
        mut index: HashMap<String, Vec<BundleIndexEntry>>,
    ) -> Result<(), String> {
        // Scan filesystem for bundles not in index
        let base_dir = index_file.parent().unwrap();
        
        for entry in fs::read_dir(base_dir)
            .map_err(|e| format!("Failed to read base directory: {}", e))?
        {
            let entry = entry
                .map_err(|e| format!("Failed to read directory entry: {}", e))?;
            
            let path = entry.path();
            if path.is_file() {
                if let Some(extension) = path.extension() {
                    if extension == "json" {
                        // Try to parse as bundle
                        if let Ok(content) = fs::read_to_string(&path) {
                            if let Ok(bundle) = serde_json::from_str::<SafetyCaseBundle>(&content) {
                                // Check if already in index
                                let session_id = &bundle.metadata.session_id;
                                let bundle_id = &bundle.metadata.bundle_id;
                                
                                let exists = index
                                    .get(session_id)
                                    .map(|bundles| bundles.iter().any(|e| e.bundle_id == *bundle_id))
                                    .unwrap_or(false);
                                
                                if !exists {
                                    let entry = BundleIndexEntry {
                                        session_id: session_id.clone(),
                                        bundle_id: bundle_id.clone(),
                                        created_at: bundle.metadata.created_at,
                                        expires_at: bundle.metadata.expires_at,
                                        file_path: path,
                                        file_size: bundle.metadata.total_size_bytes,
                                        checksum: bundle.metadata.checksum,
                                        tags: Vec::new(),
                                        metadata: HashMap::new(),
                                    };
                                    
                                    index
                                        .entry(session_id.clone())
                                        .or_insert_with(Vec::new)
                                        .push(entry);
                                }
                            }
                        }
                    }
                }
            }
        }
        
        // Save updated index
        let content = serde_json::to_string_pretty(&index)
            .map_err(|e| format!("Failed to serialize updated index: {}", e))?;
        
        fs::write(index_file, content)
            .map_err(|e| format!("Failed to write updated index: {}", e))?;
        
        Ok(())
    }

    /// Extract tags from bundle
    fn extract_tags(&self, bundle: &SafetyCaseBundle) -> Vec<String> {
        let mut tags = Vec::new();
        
        // Add capability types as tags
        for receipt in &bundle.capability_receipts {
            tags.push(format!("capability:{}", receipt.capability_id));
        }
        
        // Add plan types as tags
        for execution in &bundle.plan_executions {
            tags.push(format!("plan:{}", execution.plan_id));
        }
        
        // Add decision types as tags
        for decision in &bundle.kernel_decisions {
            tags.push(format!("decision:{}", decision.decision_type));
        }
        
        tags
    }

    /// Extract metadata from bundle
    fn extract_metadata(&self, bundle: &SafetyCaseBundle) -> HashMap<String, String> {
        let mut metadata = HashMap::new();
        
        metadata.insert("version".to_string(), bundle.metadata.version.clone());
        metadata.insert("total_components".to_string(), bundle.metadata.components.len().to_string());
        metadata.insert("capability_count".to_string(), bundle.capability_receipts.len().to_string());
        metadata.insert("plan_count".to_string(), bundle.plan_executions.len().to_string());
        metadata.insert("decision_count".to_string(), bundle.kernel_decisions.len().to_string());
        metadata.insert("certificate_count".to_string(), bundle.egress_certificates.len().to_string());
        metadata.insert("quote_count".to_string(), bundle.attestation_quotes.len().to_string());
        
        metadata
    }

    /// Check if bundle matches search criteria
    fn matches_criteria(&self, entry: &BundleIndexEntry, criteria: &SearchCriteria) -> bool {
        // Session ID filter
        if let Some(ref session_id) = criteria.session_id {
            if entry.session_id != *session_id {
                return false;
            }
        }
        
        // Bundle ID filter
        if let Some(ref bundle_id) = criteria.bundle_id {
            if entry.bundle_id != *bundle_id {
                return false;
            }
        }
        
        // Date range filter
        if let Some(after) = criteria.created_after {
            if entry.created_at < after {
                return false;
            }
        }
        
        if let Some(before) = criteria.created_before {
            if entry.created_at > before {
                return false;
            }
        }
        
        // Expiration filter
        if let Some(expires_before) = criteria.expires_before {
            if entry.expires_at > expires_before {
                return false;
            }
        }
        
        // Size filter
        if let Some(min_size) = criteria.min_size_bytes {
            if entry.file_size < min_size {
                return false;
            }
        }
        
        if let Some(max_size) = criteria.max_size_bytes {
            if entry.file_size > max_size {
                return false;
            }
        }
        
        // Tag filter
        if let Some(ref tags) = criteria.tags {
            for tag in tags {
                if !entry.tags.iter().any(|t| t.contains(tag)) {
                    return false;
                }
            }
        }
        
        true
    }

    /// Create backup of bundle
    async fn create_backup(&self, bundle_path: &Path) -> Result<(), String> {
        if let Some(ref backup_dir) = self.config.backup_directory {
            let backup_path = backup_dir.join(bundle_path.file_name().unwrap());
            
            // Create backup directory if it doesn't exist
            if let Some(parent) = backup_path.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| format!("Failed to create backup directory: {}", e))?;
            }
            
            // Copy file
            fs::copy(bundle_path, &backup_path)
                .map_err(|e| format!("Failed to create backup: {}", e))?;
        }
        
        Ok(())
    }
}

/// Search criteria for bundles
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchCriteria {
    pub session_id: Option<String>,
    pub bundle_id: Option<String>,
    pub created_after: Option<u64>,
    pub created_before: Option<u64>,
    pub expires_before: Option<u64>,
    pub min_size_bytes: Option<u64>,
    pub max_size_bytes: Option<u64>,
    pub tags: Option<Vec<String>>,
    pub sort_by: Option<String>,
    pub limit: Option<usize>,
}

impl Default for SearchCriteria {
    fn default() -> Self {
        Self {
            session_id: None,
            bundle_id: None,
            created_after: None,
            created_before: None,
            expires_before: None,
            min_size_bytes: None,
            max_size_bytes: None,
            tags: None,
            sort_by: Some("created_at".to_string()),
            limit: None,
        }
    }
}

/// Export format
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ExportFormat {
    Json,
    Yaml,
    Zip,
}

/// Store statistics
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct StoreStatistics {
    pub total_sessions: u64,
    pub total_bundles: u64,
    pub total_size_bytes: u64,
    pub oldest_bundle: u64,
    pub newest_bundle: u64,
}

/// Cleanup result
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct CleanupResult {
    pub bundles_removed: u64,
    pub sessions_removed: u64,
    pub size_freed_bytes: u64,
    pub errors: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[tokio::test]
    async fn test_safety_case_store() {
        let temp_dir = tempdir().unwrap();
        let config = StoreConfig {
            base_directory: temp_dir.path().to_path_buf(),
            ..Default::default()
        };
        
        let store = SafetyCaseStore::new(config).unwrap();
        
        // Test empty store
        let sessions = store.list_sessions().await.unwrap();
        assert_eq!(sessions.len(), 0);
        
        let stats = store.get_statistics().await.unwrap();
        assert_eq!(stats.total_sessions, 0);
        assert_eq!(stats.total_bundles, 0);
    }

    #[tokio::test]
    async fn test_bundle_storage_and_retrieval() {
        let temp_dir = tempdir().unwrap();
        let config = StoreConfig {
            base_directory: temp_dir.path().to_path_buf(),
            ..Default::default()
        };
        
        let store = SafetyCaseStore::new(config).unwrap();
        
        // Create test bundle
        let components = super::super::builder::SafetyCaseComponents::default();
        let builder = super::super::builder::SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );
        
        let bundle = builder.build(components).unwrap();
        
        // Store bundle
        let stored_path = store.store_bundle(&bundle).await.unwrap();
        assert!(stored_path.exists());
        
        // Retrieve bundle
        let retrieved_bundle = store.retrieve_bundle("test_session", "test_bundle").await.unwrap();
        assert_eq!(retrieved_bundle.metadata.session_id, "test_session");
        
        // List sessions
        let sessions = store.list_sessions().await.unwrap();
        assert_eq!(sessions.len(), 1);
        assert_eq!(sessions[0], "test_session");
        
        // List session bundles
        let bundles = store.list_session_bundles("test_session").await.unwrap();
        assert_eq!(bundles.len(), 1);
        assert_eq!(bundles[0].bundle_id, "test_bundle");
    }

    #[tokio::test]
    async fn test_search_criteria() {
        let temp_dir = tempdir().unwrap();
        let config = StoreConfig {
            base_directory: temp_dir.path().to_path_buf(),
            ..Default::default()
        };
        
        let store = SafetyCaseStore::new(config).unwrap();
        
        // Create test bundles
        let components = super::super::builder::SafetyCaseComponents::default();
        let builder = super::super::builder::SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );
        
        let bundle = builder.build(components).unwrap();
        store.store_bundle(&bundle).await.unwrap();
        
        // Search by session ID
        let criteria = SearchCriteria {
            session_id: Some("test_session".to_string()),
            ..Default::default()
        };
        
        let results = store.search_bundles(&criteria).await.unwrap();
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].session_id, "test_session");
    }
}
