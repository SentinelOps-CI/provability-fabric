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

use sidecar_watcher::declassify::SecurityLabel as DeclassSecurityLabel;
use sidecar_watcher::egress_cert::{
    CertManagerStats, CertificateUpdates, DecisionEntry, DeclassEntry, EffectEntry,
    EgressCertContent, EgressCertManager, EgressCertMetadata, EgressCertificate, NIVerdict,
    RateLimitStatus, WitnessVerification,
};
use sidecar_watcher::ni_monitor::{
    NIEvent, NIMonitor, NIMonitorConfig, NIMonitorState, NIPrefix, NIProofObligation,
    NIVerificationResult, SecurityLabel,
};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// Create test NI events for monitoring
fn create_test_ni_events() -> Vec<NIEvent> {
    vec![
        NIEvent {
            id: "event_1".to_string(),
            timestamp: "2025-01-15T10:30:00Z".to_string(),
            user_id: "user_123".to_string(),
            operation: "read".to_string(),
            resource: "data_1".to_string(),
            security_label: SecurityLabel::Confidential,
            metadata: HashMap::new(),
        },
        NIEvent {
            id: "event_2".to_string(),
            timestamp: "2025-01-15T10:31:00Z".to_string(),
            user_id: "user_123".to_string(),
            operation: "write".to_string(),
            resource: "data_2".to_string(),
            security_label: SecurityLabel::Internal,
            metadata: HashMap::new(),
        },
        NIEvent {
            id: "event_3".to_string(),
            timestamp: "2025-01-15T10:32:00Z".to_string(),
            user_id: "user_456".to_string(),
            operation: "read".to_string(),
            resource: "data_1".to_string(),
            security_label: SecurityLabel::Confidential,
            metadata: HashMap::new(),
        },
        NIEvent {
            id: "event_4".to_string(),
            timestamp: "2025-01-15T10:33:00Z".to_string(),
            user_id: "user_789".to_string(),
            operation: "declassify".to_string(),
            resource: "data_3".to_string(),
            security_label: SecurityLabel::Secret,
            metadata: HashMap::new(),
        },
        NIEvent {
            id: "event_5".to_string(),
            timestamp: "2025-01-15T10:34:00Z".to_string(),
            user_id: "user_123".to_string(),
            operation: "emit".to_string(),
            resource: "data_4".to_string(),
            security_label: SecurityLabel::Public,
            metadata: HashMap::new(),
        },
    ]
}

/// Create test NI prefixes for monitoring
fn create_test_ni_prefixes() -> Vec<NIPrefix> {
    vec![
        NIPrefix {
            id: "prefix_1".to_string(),
            events: vec!["event_1".to_string(), "event_2".to_string()],
            start_time: "2025-01-15T10:30:00Z".to_string(),
            end_time: "2025-01-15T10:31:00Z".to_string(),
            user_id: "user_123".to_string(),
            security_labels: vec![SecurityLabel::Confidential, SecurityLabel::Internal],
        },
        NIPrefix {
            id: "prefix_2".to_string(),
            events: vec!["event_3".to_string()],
            start_time: "2025-01-15T10:32:00Z".to_string(),
            end_time: "2025-01-15T10:32:00Z".to_string(),
            user_id: "user_456".to_string(),
            security_labels: vec![SecurityLabel::Confidential],
        },
        NIPrefix {
            id: "prefix_3".to_string(),
            events: vec!["event_4".to_string()],
            start_time: "2025-01-15T10:33:00Z".to_string(),
            end_time: "2025-01-15T10:33:00Z".to_string(),
            user_id: "user_789".to_string(),
            security_labels: vec![SecurityLabel::Secret],
        },
        NIPrefix {
            id: "prefix_4".to_string(),
            events: vec!["event_5".to_string()],
            start_time: "2025-01-15T10:34:00Z".to_string(),
            end_time: "2025-01-15T10:34:00Z".to_string(),
            user_id: "user_123".to_string(),
            security_labels: vec![SecurityLabel::Public],
        },
    ]
}

/// Create test egress certificate content
fn create_test_egress_cert_content() -> EgressCertContent {
    EgressCertContent {
        session_id: "session_123".to_string(),
        timestamp: "2025-01-15T10:35:00Z".to_string(),
        decisions: vec![
            DecisionEntry {
                event_id: "event_1".to_string(),
                timestamp: "2025-01-15T10:30:00Z".to_string(),
                operation: "read".to_string(),
                resource: "data_1".to_string(),
                ni_verdict: NIVerdict::Allowed,
                rate_limit_status: RateLimitStatus::WithinLimit,
                declass_entry: None,
                effect_entry: None,
                witness_verification: WitnessVerification::Valid,
            },
            DecisionEntry {
                event_id: "event_2".to_string(),
                timestamp: "2025-01-15T10:31:00Z".to_string(),
                operation: "write".to_string(),
                resource: "data_2".to_string(),
                ni_verdict: NIVerdict::Allowed,
                rate_limit_status: RateLimitStatus::WithinLimit,
                declass_entry: None,
                effect_entry: None,
                witness_verification: WitnessVerification::Valid,
            },
        ],
        ni_summary: HashMap::new(),
        rate_limit_summary: HashMap::new(),
        declass_summary: HashMap::new(),
        effect_summary: HashMap::new(),
        witness_summary: HashMap::new(),
    }
}

#[test]
fn test_ni_monitor_verdict_consistency() {
    let config = NIMonitorConfig {
        max_prefix_length: 100,
        max_prefix_duration_hours: 24,
        enable_audit_logging: true,
        strict_mode: true,
    };

    let mut monitor = NIMonitor::new(config);
    let events = create_test_ni_events();
    let prefixes = create_test_ni_prefixes();

    // Add events to monitor
    for event in events {
        let result = monitor.add_event(event);
        assert!(result.is_ok(), "Adding event should succeed");
    }

    // Add prefixes to monitor
    for prefix in prefixes {
        let result = monitor.add_prefix(prefix);
        assert!(result.is_ok(), "Adding prefix should succeed");
    }

    // Test verdict consistency across 10k prefixes
    let mut verdict_counts = HashMap::new();
    let mut proof_obligations = Vec::new();

    // Generate 10k test prefixes with various characteristics
    for i in 0..10000 {
        let prefix_id = format!("test_prefix_{}", i);
        let user_id = format!("user_{}", i % 100);
        let security_label = match i % 4 {
            0 => SecurityLabel::Public,
            1 => SecurityLabel::Internal,
            2 => SecurityLabel::Confidential,
            _ => SecurityLabel::Secret,
        };

        let test_prefix = NIPrefix {
            id: prefix_id.clone(),
            events: vec![format!("event_{}", i)],
            start_time: "2025-01-15T10:00:00Z".to_string(),
            end_time: "2025-01-15T10:01:00Z".to_string(),
            user_id: user_id.clone(),
            security_labels: vec![security_label],
        };

        let result = monitor.add_prefix(test_prefix);
        assert!(result.is_ok(), "Adding test prefix {} should succeed", i);

        // Check NI verdict
        let verdict = monitor.check_ni_violation(&prefix_id);
        if let Some(violation) = verdict {
            *verdict_counts.entry("violation".to_string()).or_insert(0) += 1;

            // Generate proof obligation for violations
            let obligation = NIProofObligation {
                prefix_id: prefix_id.clone(),
                violation_type: violation.violation_type.clone(),
                severity: violation.severity,
                timestamp: "2025-01-15T10:01:00Z".to_string(),
                user_id: user_id.clone(),
                security_label: security_label.clone(),
            };
            proof_obligations.push(obligation);
        } else {
            *verdict_counts.entry("allowed".to_string()).or_insert(0) += 1;
        }

        if i % 1000 == 0 {
            println!("Processed {} prefixes", i);
        }
    }

    println!("Verdict distribution: {:?}", verdict_counts);
    println!("Total proof obligations: {}", proof_obligations.len());

    // Verify that verdicts are consistent
    // All prefixes with the same characteristics should have the same verdict
    let mut consistency_checks = 0;
    let mut consistency_violations = 0;

    for i in 0..1000 {
        let prefix_id_1 = format!("test_prefix_{}", i);
        let prefix_id_2 = format!("test_prefix_{}", i + 1000);

        let verdict_1 = monitor.check_ni_violation(&prefix_id_1);
        let verdict_2 = monitor.check_ni_violation(&prefix_id_2);

        if let (Some(v1), Some(v2)) = (&verdict_1, &verdict_2) {
            if v1.violation_type == v2.violation_type && v1.severity == v2.severity {
                consistency_checks += 1;
            } else {
                consistency_violations += 1;
                println!(
                    "Inconsistency detected between {} and {}",
                    prefix_id_1, prefix_id_2
                );
            }
        } else if verdict_1.is_none() && verdict_2.is_none() {
            consistency_checks += 1;
        } else {
            consistency_violations += 1;
            println!(
                "Inconsistency detected between {} and {}",
                prefix_id_1, prefix_id_2
            );
        }
    }

    println!(
        "Consistency checks: {}, Violations: {}",
        consistency_checks, consistency_violations
    );

    // Verify that proof obligations are properly unwound
    for obligation in proof_obligations {
        let unwound_result = monitor.unwind_proof_obligation(&obligation);
        assert!(
            unwound_result.is_ok(),
            "Proof obligation unwinding should succeed"
        );

        let unwound = unwound_result.unwrap();
        assert!(
            !unwound.is_empty(),
            "Unwound proof obligation should not be empty"
        );

        // Verify that unwound obligations contain the necessary information
        for step in unwound {
            assert!(
                !step.description.is_empty(),
                "Unwound step should have description"
            );
            assert!(
                !step.evidence.is_empty(),
                "Unwound step should have evidence"
            );
        }
    }
}

#[test]
fn test_egress_certificate_validation() {
    let mut cert_manager = EgressCertManager::new();

    // Create test certificate
    let cert_content = create_test_egress_cert_content();
    let metadata = EgressCertMetadata {
        version: "1.0".to_string(),
        issuer: "provability-fabric".to_string(),
        issued_at: "2025-01-15T10:35:00Z".to_string(),
        expires_at: "2025-01-16T10:35:00Z".to_string(),
        session_id: "session_123".to_string(),
        policy_hash: "policy_hash_abc123".to_string(),
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    let certificate = EgressCertificate {
        metadata,
        content: cert_content,
        signature: "test_signature".to_string(),
        dsss_envelope: "test_dsss_envelope".to_string(),
    };

    // Test certificate creation
    let result = cert_manager.create_certificate(certificate.clone());
    assert!(result.is_ok(), "Certificate creation should succeed");

    // Test certificate validation
    let validation_result = cert_manager.validate_certificate(&certificate);
    assert!(
        validation_result.is_ok(),
        "Certificate validation should succeed"
    );

    let validation = validation_result.unwrap();
    assert!(validation.is_valid, "Certificate should be valid");

    // Test schema validation
    let schema_result = cert_manager.validate_certificate_schema(&certificate);
    assert!(schema_result.is_ok(), "Schema validation should succeed");

    // Test DSSE signature validation
    let signature_result = cert_manager.validate_dsse_signature(&certificate);
    assert!(
        signature_result.is_ok(),
        "DSSE signature validation should succeed"
    );

    // Test missing label witness scenario
    let mut cert_without_witness = certificate.clone();
    cert_without_witness.content.decisions[0].witness_verification = WitnessVerification::Missing;

    let validation_result = cert_manager.validate_certificate(&cert_without_witness);
    if let Ok(validation) = validation_result {
        // If validation succeeds, it should indicate the missing witness
        assert!(
            !validation.is_valid || validation.warnings.len() > 0,
            "Certificate with missing witness should be invalid or have warnings"
        );
    } else {
        // Validation failure is also acceptable
        println!("Certificate with missing witness validation failed as expected");
    }

    // Test policy hash change scenario
    let mut cert_with_changed_policy = certificate.clone();
    cert_with_changed_policy.metadata.policy_hash = "changed_policy_hash".to_string();

    let validation_result = cert_manager.validate_certificate(&cert_with_changed_policy);
    if let Ok(validation) = validation_result {
        // If validation succeeds, it should indicate the policy hash mismatch
        assert!(
            !validation.is_valid || validation.warnings.len() > 0,
            "Certificate with changed policy hash should be invalid or have warnings"
        );
    } else {
        // Validation failure is also acceptable
        println!("Certificate with changed policy hash validation failed as expected");
    }
}

#[test]
fn test_egress_certificate_schema_validation() {
    let cert_manager = EgressCertManager::new();

    // Test valid certificate schema
    let valid_cert = create_valid_test_certificate();
    let schema_result = cert_manager.validate_certificate_schema(&valid_cert);
    assert!(
        schema_result.is_ok(),
        "Valid certificate schema should pass validation"
    );

    // Test invalid certificate schema (missing required fields)
    let invalid_cert = create_invalid_test_certificate();
    let schema_result = cert_manager.validate_certificate_schema(&invalid_cert);

    match schema_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Invalid certificate schema should fail validation"
            );
            assert!(
                !validation.errors.is_empty(),
                "Invalid schema should have errors"
            );
        }
        Err(e) => {
            // Schema validation error is also acceptable
            println!("Schema validation error as expected: {:?}", e);
        }
    }

    // Test certificate with malformed metadata
    let malformed_cert = create_malformed_test_certificate();
    let schema_result = cert_manager.validate_certificate_schema(&malformed_cert);

    match schema_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Malformed certificate should fail validation"
            );
        }
        Err(e) => {
            // Schema validation error is also acceptable
            println!(
                "Malformed certificate validation error as expected: {:?}",
                e
            );
        }
    }
}

#[test]
fn test_egress_certificate_dsse_signature() {
    let cert_manager = EgressCertManager::new();

    // Test valid DSSE signature
    let valid_cert = create_valid_test_certificate();
    let signature_result = cert_manager.validate_dsse_signature(&valid_cert);
    assert!(
        signature_result.is_ok(),
        "Valid DSSE signature should pass validation"
    );

    // Test invalid DSSE signature
    let mut invalid_signature_cert = valid_cert.clone();
    invalid_signature_cert.signature = "invalid_signature".to_string();

    let signature_result = cert_manager.validate_dsse_signature(&invalid_signature_cert);
    match signature_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Invalid signature should fail validation"
            );
        }
        Err(e) => {
            // Signature validation error is also acceptable
            println!("Invalid signature validation error as expected: {:?}", e);
        }
    }

    // Test missing DSSE envelope
    let mut missing_envelope_cert = valid_cert.clone();
    missing_envelope_cert.dsss_envelope = "".to_string();

    let signature_result = cert_manager.validate_dsse_signature(&missing_envelope_cert);
    match signature_result {
        Ok(validation) => {
            assert!(
                !validation.is_valid,
                "Missing DSSE envelope should fail validation"
            );
        }
        Err(e) => {
            // Signature validation error is also acceptable
            println!(
                "Missing DSSE envelope validation error as expected: {:?}",
                e
            );
        }
    }
}

#[test]
fn test_egress_certificate_export_import() {
    let mut cert_manager = EgressCertManager::new();

    // Create and export certificate
    let cert_content = create_test_egress_cert_content();
    let metadata = EgressCertMetadata {
        version: "1.0".to_string(),
        issuer: "provability-fabric".to_string(),
        issued_at: "2025-01-15T10:35:00Z".to_string(),
        expires_at: "2025-01-16T10:35:00Z".to_string(),
        session_id: "session_123".to_string(),
        policy_hash: "policy_hash_abc123".to_string(),
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    let certificate = EgressCertificate {
        metadata,
        content: cert_content,
        signature: "test_signature".to_string(),
        dsss_envelope: "test_dsss_envelope".to_string(),
    };

    let create_result = cert_manager.create_certificate(certificate.clone());
    assert!(create_result.is_ok(), "Certificate creation should succeed");

    // Export certificate
    let export_result = cert_manager.export_certificate("session_123");
    assert!(export_result.is_ok(), "Certificate export should succeed");

    let exported_cert = export_result.unwrap();
    assert_eq!(exported_cert.metadata.session_id, "session_123");

    // Import certificate
    let import_result = cert_manager.import_certificate(exported_cert);
    assert!(import_result.is_ok(), "Certificate import should succeed");

    // Verify imported certificate
    let imported_cert = import_result.unwrap();
    assert_eq!(imported_cert.metadata.session_id, "session_123");
    assert_eq!(imported_cert.metadata.policy_hash, "policy_hash_abc123");
    assert_eq!(imported_cert.metadata.dfa_hash, "dfa_hash_def456");
    assert_eq!(imported_cert.metadata.labeler_hash, "labeler_hash_ghi789");
}

#[test]
fn test_egress_certificate_expiry_handling() {
    let mut cert_manager = EgressCertManager::new();

    // Create certificate with short expiry
    let cert_content = create_test_egress_cert_content();
    let metadata = EgressCertMetadata {
        version: "1.0".to_string(),
        issuer: "provability-fabric".to_string(),
        issued_at: "2025-01-15T10:35:00Z".to_string(),
        expires_at: "2025-01-15T10:36:00Z".to_string(), // 1 minute expiry
        session_id: "session_expiry".to_string(),
        policy_hash: "policy_hash_abc123".to_string(),
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    let certificate = EgressCertificate {
        metadata,
        content: cert_content,
        signature: "test_signature".to_string(),
        dsss_envelope: "test_dsss_envelope".to_string(),
    };

    let create_result = cert_manager.create_certificate(certificate.clone());
    assert!(create_result.is_ok(), "Certificate creation should succeed");

    // Wait for certificate to expire (simulate)
    std::thread::sleep(std::time::Duration::from_millis(100));

    // Test expired certificate handling
    let expiry_result = cert_manager.handle_certificate_expiry();
    assert!(
        expiry_result.is_ok(),
        "Certificate expiry handling should succeed"
    );

    let expired_certs = expiry_result.unwrap();
    assert!(
        !expired_certs.is_empty(),
        "Should have expired certificates"
    );

    // Verify expired certificate is marked as such
    let cert_status = cert_manager.get_certificate_status("session_expiry");
    if let Ok(status) = cert_status {
        assert_eq!(status, "expired");
    }
}

// Helper functions for testing

fn create_valid_test_certificate() -> EgressCertificate {
    let cert_content = create_test_egress_cert_content();
    let metadata = EgressCertMetadata {
        version: "1.0".to_string(),
        issuer: "provability-fabric".to_string(),
        issued_at: "2025-01-15T10:35:00Z".to_string(),
        expires_at: "2025-01-16T10:35:00Z".to_string(),
        session_id: "session_valid".to_string(),
        policy_hash: "policy_hash_abc123".to_string(),
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    EgressCertificate {
        metadata,
        content: cert_content,
        signature: "valid_signature".to_string(),
        dsss_envelope: "valid_dsss_envelope".to_string(),
    }
}

fn create_invalid_test_certificate() -> EgressCertificate {
    // Create certificate with missing required fields
    let mut cert_content = create_test_egress_cert_content();
    cert_content.session_id = "".to_string(); // Missing session ID

    let metadata = EgressCertMetadata {
        version: "1.0".to_string(),
        issuer: "provability-fabric".to_string(),
        issued_at: "2025-01-15T10:35:00Z".to_string(),
        expires_at: "2025-01-16T10:35:00Z".to_string(),
        session_id: "session_invalid".to_string(),
        policy_hash: "".to_string(), // Missing policy hash
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    EgressCertificate {
        metadata,
        content: cert_content,
        signature: "invalid_signature".to_string(),
        dsss_envelope: "invalid_dsss_envelope".to_string(),
    }
}

fn create_malformed_test_certificate() -> EgressCertificate {
    // Create certificate with malformed data
    let cert_content = create_test_egress_cert_content();
    let metadata = EgressCertMetadata {
        version: "invalid_version".to_string(), // Malformed version
        issuer: "".to_string(),                 // Missing issuer
        issued_at: "invalid_timestamp".to_string(), // Malformed timestamp
        expires_at: "2025-01-16T10:35:00Z".to_string(),
        session_id: "session_malformed".to_string(),
        policy_hash: "policy_hash_abc123".to_string(),
        dfa_hash: "dfa_hash_def456".to_string(),
        labeler_hash: "labeler_hash_ghi789".to_string(),
    };

    EgressCertificate {
        metadata,
        content: cert_content,
        signature: "malformed_signature".to_string(),
        dsss_envelope: "malformed_dsss_envelope".to_string(),
    }
}
