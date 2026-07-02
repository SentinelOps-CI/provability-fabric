/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

use sidecar_watcher::safety_case::{
    RetentionPolicy, SafetyCaseArtifact, SafetyCaseBuilder, SafetyCaseBundle, SafetyCaseConfig,
    SafetyCaseMetadata, SafetyCaseStats, SafetyCaseStore,
};
use std::collections::HashMap;

fn sample_config() -> SafetyCaseConfig {
    SafetyCaseConfig {
        bundle_retention_days: 90,
        max_bundle_size_mb: 100,
        enable_compression: true,
        enable_encryption: false,
        require_schema_validation: true,
        auto_cleanup_enabled: true,
        backup_enabled: false,
        audit_logging_enabled: true,
    }
}

fn sample_metadata(session_id: &str) -> SafetyCaseMetadata {
    SafetyCaseMetadata {
        session_id: session_id.to_string(),
        timestamp: "2025-01-15T10:30:00Z".to_string(),
        user_id: "user-1".to_string(),
        security_level: "confidential".to_string(),
        artifacts_count: 1,
        total_size_bytes: 1024,
        bundle_version: "1.0".to_string(),
        checksum: "a".repeat(64),
        retention_expiry: "2025-04-15T10:30:00Z".to_string(),
    }
}

#[test]
fn test_safety_case_bundle_creation() {
    let mut builder = SafetyCaseBuilder::new(sample_config());
    let bundle = builder
        .create_bundle("session_123", vec![], sample_metadata("session_123"))
        .unwrap();
    assert_eq!(bundle.session_id, "session_123");
}

#[test]
fn test_safety_case_store_roundtrip() {
    let mut store = SafetyCaseStore::new(sample_config());
    let bundle = SafetyCaseBundle {
        session_id: "session_456".to_string(),
        artifacts: vec![SafetyCaseArtifact {
            id: "artifact-1".to_string(),
            artifact_type: "audit".to_string(),
            content: "content".to_string(),
            hash: "hash".to_string(),
            metadata: HashMap::new(),
        }],
        metadata: sample_metadata("session_456"),
    };
    store.store_bundle(&bundle).unwrap();
    let loaded = store.retrieve_bundle("session_456").unwrap();
    assert_eq!(loaded.session_id, "session_456");
}

#[test]
fn test_retention_policy_and_stats() {
    let policy = RetentionPolicy { retain_days: 30 };
    assert_eq!(policy.retain_days, 30);
    let stats = SafetyCaseStats {
        total_bundles: 1,
        total_artifacts: 2,
    };
    assert_eq!(stats.total_bundles, 1);
}
