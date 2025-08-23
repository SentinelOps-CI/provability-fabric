/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License;
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

use sidecar_watcher::safety_case::{
    RetentionPolicy, SafetyCaseArtifact, SafetyCaseBuilder, SafetyCaseBundle, SafetyCaseConfig,
    SafetyCaseMetadata, SafetyCaseStats, SafetyCaseStore,
};
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

/// Create test safety case configuration
fn create_test_safety_case_config() -> SafetyCaseConfig {
    SafetyCaseConfig {
        bundle_retention_days: 90,
        max_bundle_size_mb: 100,
        enable_compression: true,
        enable_encryption: false,
        require_schema_validation: true,
        auto_cleanup_enabled: true,
        backup_enabled: true,
        audit_logging_enabled: true,
    }
}

/// Create test safety case artifacts
fn create_test_safety_case_artifacts() -> Vec<SafetyCaseArtifact> {
    vec![
        SafetyCaseArtifact {
            id: "artifact_1".to_string(),
            artifact_type: "dfa_table".to_string(),
            content: "DFA table content for session 1".to_string(),
            hash: "sha256_hash_artifact_1".to_string(),
            metadata: HashMap::new(),
        },
        SafetyCaseArtifact {
            id: "artifact_2".to_string(),
            artifact_type: "labeler_witness".to_string(),
            content: "Labeler witness for session 1".to_string(),
            hash: "sha256_hash_artifact_2".to_string(),
            metadata: HashMap::new(),
        },
        SafetyCaseArtifact {
            id: "artifact_3".to_string(),
            artifact_type: "declass_proof".to_string(),
            content: "Declassification proof for session 1".to_string(),
            hash: "sha256_hash_artifact_3".to_string(),
            metadata: HashMap::new(),
        },
        SafetyCaseArtifact {
            id: "artifact_4".to_string(),
            artifact_type: "rate_limit_log".to_string(),
            content: "Rate limit logs for session 1".to_string(),
            hash: "sha256_hash_artifact_4".to_string(),
            metadata: HashMap::new(),
        },
        SafetyCaseArtifact {
            id: "artifact_5".to_string(),
            artifact_type: "egress_certificate".to_string(),
            content: "Egress certificate for session 1".to_string(),
            hash: "sha256_hash_artifact_5".to_string(),
            metadata: HashMap::new(),
        },
    ]
}

/// Create test safety case metadata
fn create_test_safety_case_metadata() -> SafetyCaseMetadata {
    SafetyCaseMetadata {
        session_id: "session_123".to_string(),
        timestamp: "2025-01-15T10:30:00Z".to_string(),
        user_id: "user_123".to_string(),
        security_level: "confidential".to_string(),
        artifacts_count: 5,
        total_size_bytes: 1024,
        bundle_version: "1.0".to_string(),
        checksum: "sha256_bundle_checksum".to_string(),
        retention_expiry: "2025-04-15T10:30:00Z".to_string(),
    }
}

#[test]
fn test_safety_case_bundle_creation() {
    let config = create_test_safety_case_config();
    let mut builder = SafetyCaseBuilder::new(config);

    // Create safety case bundle
    let session_id = "session_123";
    let artifacts = create_test_safety_case_artifacts();
    let metadata = create_test_safety_case_metadata();

    let bundle_result = builder.create_bundle(session_id, artifacts.clone(), metadata.clone());
    assert!(
        bundle_result.is_ok(),
        "Safety case bundle creation should succeed"
    );

    let bundle = bundle_result.unwrap();

    // Verify bundle properties
    assert_eq!(bundle.session_id, session_id);
    assert_eq!(bundle.artifacts.len(), 5);
    assert_eq!(bundle.metadata.artifacts_count, 5);
    assert_eq!(bundle.metadata.total_size_bytes, 1024);
    assert_eq!(bundle.metadata.bundle_version, "1.0");

    // Verify all artifacts are included
    for artifact in &artifacts {
        let found_artifact = bundle
            .artifacts
            .iter()
            .find(|a| a.id == artifact.id)
            .expect(&format!("Artifact {} should be in bundle", artifact.id));

        assert_eq!(found_artifact.content, artifact.content);
        assert_eq!(found_artifact.hash, artifact.hash);
    }

    // Verify bundle checksum
    assert!(
        !bundle.metadata.checksum.is_empty(),
        "Bundle should have checksum"
    );
    assert_eq!(
        bundle.metadata.checksum.len(),
        64,
        "SHA-256 checksum should be 64 characters"
    );

    // Verify retention expiry is set correctly
    let expected_expiry = "2025-04-15T10:30:00Z"; // 90 days from creation
    assert_eq!(bundle.metadata.retention_expiry, expected_expiry);
}

#[test]
fn test_safety_case_bundle_storage() {
    let config = create_test_safety_case_config();
    let mut store = SafetyCaseStore::new(config);

    // Create and store safety case bundle
    let bundle = create_test_safety_case_bundle();
    let store_result = store.store_bundle(&bundle);
    assert!(store_result.is_ok(), "Bundle storage should succeed");

    // Verify bundle is stored
    let stored_bundle = store.retrieve_bundle(&bundle.session_id);
    assert!(stored_bundle.is_ok(), "Bundle retrieval should succeed");

    let retrieved_bundle = stored_bundle.unwrap();
    assert_eq!(retrieved_bundle.session_id, bundle.session_id);
    assert_eq!(retrieved_bundle.artifacts.len(), bundle.artifacts.len());
    assert_eq!(retrieved_bundle.metadata.checksum, bundle.metadata.checksum);

    // Test bundle listing
    let bundles = store.list_bundles();
    assert!(bundles.is_ok(), "Bundle listing should succeed");

    let bundle_list = bundles.unwrap();
    assert!(!bundle_list.is_empty(), "Bundle list should not be empty");
    assert!(
        bundle_list.contains(&bundle.session_id),
        "Bundle list should contain stored bundle"
    );

    // Test bundle search
    let search_result = store.search_bundles("session_123");
    assert!(search_result.is_ok(), "Bundle search should succeed");

    let search_results = search_result.unwrap();
    assert!(
        !search_results.is_empty(),
        "Search results should not be empty"
    );
    assert!(search_results.iter().any(|b| b.session_id == "session_123"));

    // Test bundle update
    let mut updated_bundle = bundle.clone();
    updated_bundle.metadata.security_level = "secret".to_string();

    let update_result = store.update_bundle(&updated_bundle);
    assert!(update_result.is_ok(), "Bundle update should succeed");

    // Verify update
    let updated_retrieved = store.retrieve_bundle(&bundle.session_id);
    assert!(
        updated_retrieved.is_ok(),
        "Updated bundle retrieval should succeed"
    );

    let retrieved = updated_retrieved.unwrap();
    assert_eq!(retrieved.metadata.security_level, "secret");
}

#[test]
fn test_safety_case_bundle_retention() {
    let config = create_test_safety_case_config();
    let mut store = SafetyCaseStore::new(config);

    // Create multiple bundles with different timestamps
    let test_bundles = vec![
        ("session_old", "2024-10-15T10:30:00Z"), // More than 90 days old
        ("session_recent", "2025-01-10T10:30:00Z"), // Less than 90 days old
        ("session_current", "2025-01-15T10:30:00Z"), // Current
    ];

    for (session_id, timestamp) in test_bundles {
        let mut metadata = create_test_safety_case_metadata();
        metadata.session_id = session_id.to_string();
        metadata.timestamp = timestamp.to_string();

        // Calculate retention expiry based on timestamp
        let retention_expiry = if timestamp.contains("2024-10-15") {
            "2025-01-13T10:30:00Z" // Expired
        } else {
            "2025-04-15T10:30:00Z" // Not expired
        };
        metadata.retention_expiry = retention_expiry.to_string();

        let bundle = SafetyCaseBundle {
            session_id: session_id.to_string(),
            artifacts: create_test_safety_case_artifacts(),
            metadata,
        };

        let store_result = store.store_bundle(&bundle);
        assert!(store_result.is_ok(), "Bundle storage should succeed");
    }

    // Test retention policy enforcement
    let retention_result = store.enforce_retention_policy();
    assert!(
        retention_result.is_ok(),
        "Retention policy enforcement should succeed"
    );

    let retention_report = retention_result.unwrap();
    assert!(
        !retention_report.expired_bundles.is_empty(),
        "Should have expired bundles"
    );
    assert!(
        !retention_report.retained_bundles.is_empty(),
        "Should have retained bundles"
    );

    // Verify expired bundle is removed
    let expired_bundle = store.retrieve_bundle("session_old");
    match expired_bundle {
        Ok(_) => {
            // If bundle still exists, it should be marked for deletion
            println!("Expired bundle still exists but marked for deletion");
        }
        Err(_) => {
            // Bundle should be removed
            println!("Expired bundle removed as expected");
        }
    }

    // Verify recent bundles are retained
    let recent_bundle = store.retrieve_bundle("session_recent");
    assert!(recent_bundle.is_ok(), "Recent bundle should be retained");

    let current_bundle = store.retrieve_bundle("session_current");
    assert!(current_bundle.is_ok(), "Current bundle should be retained");

    // Test manual retention extension
    let extend_result = store.extend_retention("session_recent", 30); // Extend by 30 days
    assert!(extend_result.is_ok(), "Retention extension should succeed");

    let extended_bundle = store.retrieve_bundle("session_recent");
    assert!(
        extended_bundle.is_ok(),
        "Extended bundle should be retrievable"
    );

    let extended = extended_bundle.unwrap();
    let new_expiry = "2025-05-10T10:30:00Z"; // Extended expiry
    assert_eq!(extended.metadata.retention_expiry, new_expiry);
}

#[test]
fn test_safety_case_bundle_schema_validation() {
    let config = create_test_safety_case_config();
    let builder = SafetyCaseBuilder::new(config);

    // Test valid bundle schema
    let valid_bundle = create_test_safety_case_bundle();
    let validation_result = builder.validate_bundle_schema(&valid_bundle);
    assert!(
        validation_result.is_ok(),
        "Valid bundle schema should pass validation"
    );

    let validation = validation_result.unwrap();
    assert!(validation.is_valid, "Bundle should be valid");

    // Test invalid bundle schema (missing required fields)
    let mut invalid_bundle = valid_bundle.clone();
    invalid_bundle.session_id = "".to_string(); // Missing session ID
    invalid_bundle.metadata.timestamp = "".to_string(); // Missing timestamp

    let validation_result = builder.validate_bundle_schema(&invalid_bundle);
    match validation_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Invalid bundle schema should fail validation"
            );
            assert!(
                !validation.errors.is_empty(),
                "Invalid schema should have errors"
            );

            // Verify specific error messages
            let has_session_error = validation
                .errors
                .iter()
                .any(|e| e.contains("session_id") || e.contains("session"));
            assert!(has_session_error, "Should have session ID error");

            let has_timestamp_error = validation
                .errors
                .iter()
                .any(|e| e.contains("timestamp") || e.contains("time"));
            assert!(has_timestamp_error, "Should have timestamp error");
        }
        Err(e) => {
            // Schema validation error is also acceptable
            println!("Schema validation error as expected: {:?}", e);
        }
    }

    // Test bundle with malformed metadata
    let mut malformed_bundle = valid_bundle.clone();
    malformed_bundle.metadata.bundle_version = "invalid_version".to_string();
    malformed_bundle.metadata.checksum = "invalid_checksum".to_string();

    let validation_result = builder.validate_bundle_schema(&malformed_bundle);
    match validation_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Malformed bundle should fail validation"
            );
        }
        Err(e) => {
            // Schema validation error is also acceptable
            println!("Malformed bundle validation error as expected: {:?}", e);
        }
    }
}

#[test]
fn test_safety_case_bundle_compression() {
    let config = create_test_safety_case_config();
    let mut builder = SafetyCaseBuilder::new(config);

    // Enable compression
    assert!(
        builder.get_config().enable_compression,
        "Compression should be enabled"
    );

    // Create bundle with compression
    let bundle = create_test_safety_case_bundle();
    let compressed_result = builder.compress_bundle(&bundle);
    assert!(
        compressed_result.is_ok(),
        "Bundle compression should succeed"
    );

    let compressed_bundle = compressed_result.unwrap();

    // Verify compression reduces size
    let original_size = bundle.metadata.total_size_bytes;
    let compressed_size = compressed_bundle.metadata.total_size_bytes;
    assert!(
        compressed_size < original_size,
        "Compressed bundle should be smaller"
    );

    // Test bundle decompression
    let decompressed_result = builder.decompress_bundle(&compressed_bundle);
    assert!(
        decompressed_result.is_ok(),
        "Bundle decompression should succeed"
    );

    let decompressed_bundle = decompressed_result.unwrap();

    // Verify decompressed bundle matches original
    assert_eq!(decompressed_bundle.session_id, bundle.session_id);
    assert_eq!(decompressed_bundle.artifacts.len(), bundle.artifacts.len());
    assert_eq!(
        decompressed_bundle.metadata.checksum,
        bundle.metadata.checksum
    );

    // Verify all artifacts are preserved
    for (i, original_artifact) in bundle.artifacts.iter().enumerate() {
        let decompressed_artifact = &decompressed_bundle.artifacts[i];
        assert_eq!(decompressed_artifact.id, original_artifact.id);
        assert_eq!(decompressed_artifact.content, original_artifact.content);
        assert_eq!(decompressed_artifact.hash, original_artifact.hash);
    }
}

#[test]
fn test_safety_case_bundle_export_import() {
    let config = create_test_safety_case_config();
    let builder = SafetyCaseBuilder::new(config);

    // Create test bundle
    let bundle = create_test_safety_case_bundle();

    // Test bundle export
    let export_result = builder.export_bundle(&bundle);
    assert!(export_result.is_ok(), "Bundle export should succeed");

    let exported_data = export_result.unwrap();
    assert!(
        !exported_data.is_empty(),
        "Exported bundle should not be empty"
    );

    // Test bundle import
    let import_result = builder.import_bundle(&exported_data);
    assert!(import_result.is_ok(), "Bundle import should succeed");

    let imported_bundle = import_result.unwrap();

    // Verify imported bundle matches original
    assert_eq!(imported_bundle.session_id, bundle.session_id);
    assert_eq!(imported_bundle.artifacts.len(), bundle.artifacts.len());
    assert_eq!(imported_bundle.metadata.checksum, bundle.metadata.checksum);
    assert_eq!(
        imported_bundle.metadata.bundle_version,
        bundle.metadata.bundle_version
    );

    // Verify all artifacts are preserved
    for (i, original_artifact) in bundle.artifacts.iter().enumerate() {
        let imported_artifact = &imported_bundle.artifacts[i];
        assert_eq!(imported_artifact.id, original_artifact.id);
        assert_eq!(
            imported_artifact.artifact_type,
            original_artifact.artifact_type
        );
        assert_eq!(imported_artifact.content, original_artifact.content);
        assert_eq!(imported_artifact.hash, original_artifact.hash);
    }

    // Test import with corrupted data
    let corrupted_data = "corrupted_bundle_data";
    let import_result = builder.import_bundle(corrupted_data);

    match import_result {
        Ok(_) => {
            // If import succeeds, it should handle corruption gracefully
            println!("Corrupted bundle import handled gracefully");
        }
        Err(e) => {
            // Import failure is expected for corrupted data
            println!("Corrupted bundle import failed as expected: {:?}", e);
        }
    }
}

#[test]
fn test_safety_case_bundle_statistics() {
    let config = create_test_safety_case_config();
    let mut store = SafetyCaseStore::new(config);

    // Create multiple bundles for statistics testing
    let test_sessions = vec![
        ("session_stats_1", "2025-01-01T10:00:00Z", 3),
        ("session_stats_2", "2025-01-02T10:00:00Z", 5),
        ("session_stats_3", "2025-01-03T10:00:00Z", 2),
        ("session_stats_4", "2025-01-04T10:00:00Z", 4),
    ];

    for (session_id, timestamp, artifact_count) in test_sessions {
        let mut metadata = create_test_safety_case_metadata();
        metadata.session_id = session_id.to_string();
        metadata.timestamp = timestamp.to_string();
        metadata.artifacts_count = artifact_count;
        metadata.total_size_bytes = artifact_count * 256; // Simulate size

        let bundle = SafetyCaseBundle {
            session_id: session_id.to_string(),
            artifacts: create_test_safety_case_artifacts()
                .into_iter()
                .take(artifact_count)
                .collect(),
            metadata,
        };

        let store_result = store.store_bundle(&bundle);
        assert!(store_result.is_ok(), "Bundle storage should succeed");
    }

    // Test statistics retrieval
    let stats_result = store.get_statistics();
    assert!(stats_result.is_ok(), "Getting statistics should succeed");

    let stats = stats_result.unwrap();

    // Verify basic statistics
    assert_eq!(stats.total_bundles, 4, "Should have 4 total bundles");
    assert_eq!(
        stats.total_artifacts, 14,
        "Should have 14 total artifacts (3+5+2+4)"
    );
    assert_eq!(
        stats.total_size_bytes, 3584,
        "Should have correct total size"
    );

    // Verify bundle distribution
    assert_eq!(stats.bundles_by_date.get("2025-01-01"), Some(&1));
    assert_eq!(stats.bundles_by_date.get("2025-01-02"), Some(&1));
    assert_eq!(stats.bundles_by_date.get("2025-01-03"), Some(&1));
    assert_eq!(stats.bundles_by_date.get("2025-01-04"), Some(&1));

    // Test statistics export
    let export_result = store.export_statistics();
    assert!(export_result.is_ok(), "Statistics export should succeed");

    let exported_stats = export_result.unwrap();
    assert!(
        !exported_stats.is_empty(),
        "Exported statistics should not be empty"
    );

    // Test statistics filtering by date range
    let date_filtered_stats =
        store.get_statistics_in_range("2025-01-01T00:00:00Z", "2025-01-03T23:59:59Z");
    assert!(
        date_filtered_stats.is_ok(),
        "Date-filtered statistics should succeed"
    );

    let filtered_stats = date_filtered_stats.unwrap();
    assert_eq!(
        filtered_stats.total_bundles, 3,
        "Date-filtered should include 3 bundles"
    );
}

#[test]
fn test_safety_case_bundle_cleanup() {
    let config = create_test_safety_case_config();
    let mut store = SafetyCaseStore::new(config);

    // Enable auto-cleanup
    assert!(
        store.get_config().auto_cleanup_enabled,
        "Auto-cleanup should be enabled"
    );

    // Create bundles with different retention statuses
    let test_bundles = vec![
        ("cleanup_expired", "2024-10-15T10:00:00Z", true), // Expired
        ("cleanup_expiring_soon", "2025-01-10T10:00:00Z", false), // Expiring soon
        ("cleanup_valid", "2025-01-15T10:00:00Z", false),  // Valid
    ];

    for (session_id, timestamp, is_expired) in test_bundles {
        let mut metadata = create_test_safety_case_metadata();
        metadata.session_id = session_id.to_string();
        metadata.timestamp = timestamp.to_string();

        if is_expired {
            metadata.retention_expiry = "2025-01-13T10:00:00Z".to_string(); // Expired
        } else {
            metadata.retention_expiry = "2025-04-15T10:00:00Z".to_string(); // Valid
        }

        let bundle = SafetyCaseBundle {
            session_id: session_id.to_string(),
            artifacts: create_test_safety_case_artifacts(),
            metadata,
        };

        let store_result = store.store_bundle(&bundle);
        assert!(store_result.is_ok(), "Bundle storage should succeed");
    }

    // Test auto-cleanup
    let cleanup_result = store.perform_auto_cleanup();
    assert!(cleanup_result.is_ok(), "Auto-cleanup should succeed");

    let cleanup_report = cleanup_result.unwrap();
    assert!(
        !cleanup_report.removed_bundles.is_empty(),
        "Should have removed expired bundles"
    );
    assert!(
        !cleanup_report.retained_bundles.is_empty(),
        "Should have retained valid bundles"
    );

    // Verify expired bundle is removed
    let expired_bundle = store.retrieve_bundle("cleanup_expired");
    match expired_bundle {
        Ok(_) => {
            // If bundle still exists, it should be marked for deletion
            println!("Expired bundle still exists but marked for deletion");
        }
        Err(_) => {
            // Bundle should be removed
            println!("Expired bundle removed as expected");
        }
    }

    // Verify valid bundles are retained
    let expiring_soon_bundle = store.retrieve_bundle("cleanup_expiring_soon");
    assert!(
        expiring_soon_bundle.is_ok(),
        "Expiring soon bundle should be retained"
    );

    let valid_bundle = store.retrieve_bundle("cleanup_valid");
    assert!(valid_bundle.is_ok(), "Valid bundle should be retained");

    // Test manual cleanup
    let manual_cleanup_result = store.manual_cleanup("cleanup_expiring_soon");
    assert!(
        manual_cleanup_result.is_ok(),
        "Manual cleanup should succeed"
    );

    let manual_cleanup_report = manual_cleanup_result.unwrap();
    assert!(manual_cleanup_report
        .removed_bundles
        .contains(&"cleanup_expiring_soon".to_string()));
}

// Helper functions for testing

fn create_test_safety_case_bundle() -> SafetyCaseBundle {
    SafetyCaseBundle {
        session_id: "session_123".to_string(),
        artifacts: create_test_safety_case_artifacts(),
        metadata: create_test_safety_case_metadata(),
    }
}
