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

//! Safety Case Bundle Management
//! 
//! This module provides comprehensive safety case bundle management for Provability Fabric.
//! It includes:
//! 
//! - **Builder**: Creates and validates safety case bundles
//! - **Store**: Manages storage, retrieval, and search of safety case bundles
//! - **Components**: Defines the structure of safety case bundles
//! 
//! ## Safety Case Bundle Structure
//! 
//! A safety case bundle contains:
//! - Session metadata and expiration
//! - Capability receipts with signatures
//! - Plan execution records
//! - Kernel decision logs
//! - Egress certificates
//! - Attestation quotes
//! - Binary artifacts
//! 
//! ## Usage Example
//! 
//! ```rust
//! use runtime::ledger::safety_case::{SafetyCaseBuilder, SafetyCaseStore, StoreConfig};
//! 
//! // Create store
//! let config = StoreConfig::default();
//! let store = SafetyCaseStore::new(config).await?;
//! 
//! // Build bundle
//! let builder = SafetyCaseBuilder::new(
//!     "session_123".to_string(),
//!     "bundle_456".to_string(),
//!     PathBuf::from("./output"),
//! );
//! 
//! let components = SafetyCaseComponents::default();
//! let bundle = builder.build(components)?;
//! 
//! // Store bundle
//! let path = store.store_bundle(&bundle).await?;
//! 
//! // Retrieve bundle
//! let retrieved = store.retrieve_bundle("session_123", "bundle_456").await?;
//! 
//! // Search bundles
//! let criteria = SearchCriteria {
//!     session_id: Some("session_123".to_string()),
//!     ..Default::default()
//! };
//! let results = store.search_bundles(&criteria).await?;
//! ```
//! 
//! ## Retention Policy
//! 
//! Safety case bundles are automatically cleaned up based on their expiration time.
//! The default retention period is 90 days, but this can be configured per store.
//! 
//! ## Backup and Recovery
//! 
//! The store supports automatic backup creation and can recover from filesystem
//! inconsistencies by rebuilding the index from actual bundle files.

pub mod builder;
pub mod store;

pub use builder::{
    SafetyCaseBundle, SafetyCaseBuilder, SafetyCaseComponents, SafetyCaseMetadata,
    CapabilityReceipt, PlanExecutionRecord, KernelDecisionLog, EgressCertificate,
    AttestationQuote,
};
pub use store::{
    SafetyCaseStore, StoreConfig, BundleIndexEntry, SearchCriteria, ExportFormat,
    StoreStatistics, CleanupResult,
};

/// Re-export commonly used types
pub type Bundle = SafetyCaseBundle;
pub type Store = SafetyCaseStore;
pub type Builder = SafetyCaseBuilder;

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    use std::path::PathBuf;

    #[tokio::test]
    async fn test_safety_case_integration() {
        let temp_dir = tempdir().unwrap();
        let config = StoreConfig {
            base_directory: temp_dir.path().to_path_buf(),
            ..Default::default()
        };
        
        let store = SafetyCaseStore::new(config).await.unwrap();
        
        // Create test bundle
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );
        
        let components = SafetyCaseComponents::default();
        let bundle = builder.build(components).unwrap();
        
        // Store and retrieve
        let stored_path = store.store_bundle(&bundle).await.unwrap();
        assert!(stored_path.exists());
        
        let retrieved = store.retrieve_bundle("test_session", "test_bundle").await.unwrap();
        assert_eq!(retrieved.metadata.session_id, "test_session");
        assert_eq!(retrieved.metadata.bundle_id, "test_bundle");
    }

    #[test]
    fn test_bundle_serialization() {
        let components = SafetyCaseComponents::default();
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            PathBuf::from("./test"),
        );
        
        let bundle = builder.build(components).unwrap();
        
        // Test JSON serialization
        let json = serde_json::to_string_pretty(&bundle).unwrap();
        let deserialized: SafetyCaseBundle = serde_json::from_str(&json).unwrap();
        
        assert_eq!(bundle.metadata.session_id, deserialized.metadata.session_id);
        assert_eq!(bundle.metadata.bundle_id, deserialized.metadata.bundle_id);
        assert_eq!(bundle.metadata.checksum, deserialized.metadata.checksum);
    }
}
