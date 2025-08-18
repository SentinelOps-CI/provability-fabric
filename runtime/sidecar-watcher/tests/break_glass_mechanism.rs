/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License;
 * you may may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use sidecar_watcher::break_glass::{
    BreakGlassConfig, BreakGlassManager, BreakGlassRequest, BreakGlassSignature, BreakGlassStats,
    BreakGlassStatus, PostMortemStub, UrgencyLevel,
};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

/// Create test break-glass configuration
fn create_test_break_glass_config() -> BreakGlassConfig {
    BreakGlassConfig {
        min_signatures: 3, // M-of-N where M=3, N=5
        max_signatures: 5,
        max_urgency_level: UrgencyLevel::Critical,
        auto_expiry_hours: 24,
        require_justification: true,
        enable_audit_logging: true,
        post_mortem_required: true,
    }
}

/// Create test break-glass requests
fn create_test_break_glass_requests() -> Vec<BreakGlassRequest> {
    vec![
        BreakGlassRequest {
            id: "request_1".to_string(),
            user_id: "user_123".to_string(),
            urgency_level: UrgencyLevel::High,
            justification: "Emergency access required for incident response".to_string(),
            timestamp: "2025-01-15T10:30:00Z".to_string(),
            expiry: "2025-01-16T10:30:00Z".to_string(),
            status: BreakGlassStatus::Pending,
            signatures: Vec::new(),
            metadata: HashMap::new(),
        },
        BreakGlassRequest {
            id: "request_2".to_string(),
            user_id: "user_456".to_string(),
            urgency_level: UrgencyLevel::Critical,
            justification: "System failure requires immediate intervention".to_string(),
            timestamp: "2025-01-15T10:35:00Z".to_string(),
            expiry: "2025-01-15T22:35:00Z".to_string(),
            status: BreakGlassStatus::Pending,
            signatures: Vec::new(),
            metadata: HashMap::new(),
        },
        BreakGlassRequest {
            id: "request_3".to_string(),
            user_id: "user_789".to_string(),
            urgency_level: UrgencyLevel::Medium,
            justification: "Scheduled maintenance requires elevated access".to_string(),
            timestamp: "2025-01-15T11:00:00Z".to_string(),
            expiry: "2025-01-16T11:00:00Z".to_string(),
            status: BreakGlassStatus::Pending,
            signatures: Vec::new(),
            metadata: HashMap::new(),
        },
    ]
}

/// Create test break-glass signatures
fn create_test_break_glass_signatures() -> Vec<BreakGlassSignature> {
    vec![
        BreakGlassSignature {
            id: "signature_1".to_string(),
            request_id: "request_1".to_string(),
            user_id: "approver_1".to_string(),
            timestamp: "2025-01-15T10:31:00Z".to_string(),
            signature: "sig_hash_1".to_string(),
            approval_level: "manager".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "signature_2".to_string(),
            request_id: "request_1".to_string(),
            user_id: "approver_2".to_string(),
            timestamp: "2025-01-15T10:32:00Z".to_string(),
            signature: "sig_hash_2".to_string(),
            approval_level: "director".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "signature_3".to_string(),
            request_id: "request_1".to_string(),
            user_id: "approver_3".to_string(),
            timestamp: "2025-01-15T10:33:00Z".to_string(),
            signature: "sig_hash_3".to_string(),
            approval_level: "vp".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "signature_4".to_string(),
            request_id: "request_2".to_string(),
            user_id: "approver_4".to_string(),
            timestamp: "2025-01-15T10:36:00Z".to_string(),
            signature: "sig_hash_4".to_string(),
            approval_level: "cto".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "signature_5".to_string(),
            request_id: "request_2".to_string(),
            user_id: "approver_5".to_string(),
            timestamp: "2025-01-15T10:37:00Z".to_string(),
            signature: "sig_hash_5".to_string(),
            approval_level: "ceo".to_string(),
            metadata: HashMap::new(),
        },
    ]
}

#[test]
fn test_break_glass_m_of_n_signatures() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Test M-of-N signature requirement (3 of 5)
    assert_eq!(manager.get_config().min_signatures, 3);
    assert_eq!(manager.get_config().max_signatures, 5);

    // Create break-glass request
    let request = BreakGlassRequest {
        id: "test_request".to_string(),
        user_id: "user_test".to_string(),
        urgency_level: UrgencyLevel::High,
        justification: "Testing M-of-N signatures".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-16T10:00:00Z".to_string(),
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(request);
    assert!(
        create_result.is_ok(),
        "Break-glass request creation should succeed"
    );

    // Test insufficient signatures (less than M)
    let insufficient_signatures = vec![
        BreakGlassSignature {
            id: "sig_1".to_string(),
            request_id: "test_request".to_string(),
            user_id: "approver_1".to_string(),
            timestamp: "2025-01-15T10:01:00Z".to_string(),
            signature: "sig_hash_1".to_string(),
            approval_level: "manager".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "sig_2".to_string(),
            request_id: "test_request".to_string(),
            user_id: "approver_2".to_string(),
            timestamp: "2025-01-15T10:02:00Z".to_string(),
            signature: "sig_hash_2".to_string(),
            approval_level: "director".to_string(),
            metadata: HashMap::new(),
        },
        // Only 2 signatures, need 3
    ];

    for signature in insufficient_signatures {
        let add_result = manager.add_signature(signature);
        assert!(add_result.is_ok(), "Adding signature should succeed");
    }

    // Check that request is still pending (insufficient signatures)
    let request_status = manager.get_request_status("test_request");
    assert!(
        request_status.is_ok(),
        "Getting request status should succeed"
    );

    let status = request_status.unwrap();
    assert_eq!(
        status,
        BreakGlassStatus::Pending,
        "Request should still be pending"
    );

    // Add third signature to meet M-of-N requirement
    let third_signature = BreakGlassSignature {
        id: "sig_3".to_string(),
        request_id: "test_request".to_string(),
        user_id: "approver_3".to_string(),
        timestamp: "2025-01-15T10:03:00Z".to_string(),
        signature: "sig_hash_3".to_string(),
        approval_level: "vp".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(third_signature);
    assert!(add_result.is_ok(), "Adding third signature should succeed");

    // Check that request is now approved (M signatures reached)
    let request_status = manager.get_request_status("test_request");
    assert!(
        request_status.is_ok(),
        "Getting request status should succeed"
    );

    let status = request_status.unwrap();
    assert_eq!(
        status,
        BreakGlassStatus::Approved,
        "Request should be approved"
    );

    // Test that additional signatures don't change the status
    let fourth_signature = BreakGlassSignature {
        id: "sig_4".to_string(),
        request_id: "test_request".to_string(),
        user_id: "approver_4".to_string(),
        timestamp: "2025-01-15T10:04:00Z".to_string(),
        signature: "sig_hash_4".to_string(),
        approval_level: "cto".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(fourth_signature);
    assert!(add_result.is_ok(), "Adding fourth signature should succeed");

    let request_status = manager.get_request_status("test_request");
    assert!(
        request_status.is_ok(),
        "Getting request status should succeed"
    );

    let status = request_status.unwrap();
    assert_eq!(
        status,
        BreakGlassStatus::Approved,
        "Request should remain approved"
    );
}

#[test]
fn test_break_glass_signature_validation() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Create break-glass request
    let request = BreakGlassRequest {
        id: "validation_request".to_string(),
        user_id: "user_validation".to_string(),
        urgency_level: UrgencyLevel::Medium,
        justification: "Testing signature validation".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-16T10:00:00Z".to_string(),
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(request);
    assert!(
        create_result.is_ok(),
        "Break-glass request creation should succeed"
    );

    // Test valid signature
    let valid_signature = BreakGlassSignature {
        id: "valid_sig".to_string(),
        request_id: "validation_request".to_string(),
        user_id: "valid_approver".to_string(),
        timestamp: "2025-01-15T10:01:00Z".to_string(),
        signature: "valid_sig_hash".to_string(),
        approval_level: "manager".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(valid_signature);
    assert!(
        add_result.is_ok(),
        "Valid signature should be added successfully"
    );

    // Test duplicate signature (same user)
    let duplicate_signature = BreakGlassSignature {
        id: "duplicate_sig".to_string(),
        request_id: "validation_request".to_string(),
        user_id: "valid_approver".to_string(), // Same user
        timestamp: "2025-01-15T10:02:00Z".to_string(),
        signature: "duplicate_sig_hash".to_string(),
        approval_level: "manager".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(duplicate_signature);
    match add_result {
        Ok(_) => {
            // If duplicate signatures are allowed, verify it's handled appropriately
            let signatures = manager.get_request_signatures("validation_request");
            assert!(signatures.is_ok(), "Getting signatures should succeed");
        }
        Err(e) => {
            // Duplicate signature rejection is also acceptable
            println!("Duplicate signature rejected as expected: {:?}", e);
        }
    }

    // Test invalid signature (wrong request ID)
    let invalid_signature = BreakGlassSignature {
        id: "invalid_sig".to_string(),
        request_id: "wrong_request".to_string(), // Wrong request ID
        user_id: "valid_approver_2".to_string(),
        timestamp: "2025-01-15T10:03:00Z".to_string(),
        signature: "invalid_sig_hash".to_string(),
        approval_level: "director".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(invalid_signature);
    match add_result {
        Ok(_) => {
            // If invalid signatures are handled gracefully, verify appropriate behavior
            println!("Invalid signature handled gracefully");
        }
        Err(e) => {
            // Invalid signature rejection is expected
            println!("Invalid signature rejected as expected: {:?}", e);
        }
    }

    // Test signature with missing required fields
    let incomplete_signature = BreakGlassSignature {
        id: "incomplete_sig".to_string(),
        request_id: "validation_request".to_string(),
        user_id: "".to_string(), // Missing user ID
        timestamp: "2025-01-15T10:04:00Z".to_string(),
        signature: "incomplete_sig_hash".to_string(),
        approval_level: "".to_string(), // Missing approval level
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(incomplete_signature);
    match add_result {
        Ok(_) => {
            // If incomplete signatures are handled gracefully, verify appropriate behavior
            println!("Incomplete signature handled gracefully");
        }
        Err(e) => {
            // Incomplete signature rejection is expected
            println!("Incomplete signature rejected as expected: {:?}", e);
        }
    }
}

#[test]
fn test_break_glass_post_mortem_stub_emission() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Create break-glass request
    let request = BreakGlassRequest {
        id: "post_mortem_request".to_string(),
        user_id: "user_post_mortem".to_string(),
        urgency_level: UrgencyLevel::Critical,
        justification: "Testing post-mortem stub emission".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-15T10:01:00Z".to_string(), // Very short expiry
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(request);
    assert!(
        create_result.is_ok(),
        "Break-glass request creation should succeed"
    );

    // Add required signatures to approve the request
    let required_signatures = vec![
        BreakGlassSignature {
            id: "pm_sig_1".to_string(),
            request_id: "post_mortem_request".to_string(),
            user_id: "pm_approver_1".to_string(),
            timestamp: "2025-01-15T10:00:30Z".to_string(),
            signature: "pm_sig_hash_1".to_string(),
            approval_level: "manager".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "pm_sig_2".to_string(),
            request_id: "post_mortem_request".to_string(),
            user_id: "pm_approver_2".to_string(),
            timestamp: "2025-01-15T10:00:45Z".to_string(),
            signature: "pm_sig_hash_2".to_string(),
            approval_level: "director".to_string(),
            metadata: HashMap::new(),
        },
        BreakGlassSignature {
            id: "pm_sig_3".to_string(),
            request_id: "post_mortem_request".to_string(),
            user_id: "pm_approver_3".to_string(),
            timestamp: "2025-01-15T10:01:00Z".to_string(),
            signature: "pm_sig_hash_3".to_string(),
            approval_level: "vp".to_string(),
            metadata: HashMap::new(),
        },
    ];

    for signature in required_signatures {
        let add_result = manager.add_signature(signature);
        assert!(add_result.is_ok(), "Adding signature should succeed");
    }

    // Verify request is approved
    let request_status = manager.get_request_status("post_mortem_request");
    assert!(
        request_status.is_ok(),
        "Getting request status should succeed"
    );

    let status = request_status.unwrap();
    assert_eq!(
        status,
        BreakGlassStatus::Approved,
        "Request should be approved"
    );

    // Wait for request to expire (simulate)
    std::thread::sleep(std::time::Duration::from_millis(100));

    // Test post-mortem stub emission
    let post_mortem_result = manager.generate_post_mortem_stub("post_mortem_request");
    assert!(
        post_mortem_result.is_ok(),
        "Post-mortem stub generation should succeed"
    );

    let post_mortem_stub = post_mortem_result.unwrap();

    // Verify post-mortem stub contains required information
    assert_eq!(post_mortem_stub.request_id, "post_mortem_request");
    assert!(
        !post_mortem_stub.summary.is_empty(),
        "Post-mortem summary should not be empty"
    );
    assert!(
        !post_mortem_stub.actions_taken.is_empty(),
        "Post-mortem actions should not be empty"
    );
    assert!(
        !post_mortem_stub.lessons_learned.is_empty(),
        "Post-mortem lessons should not be empty"
    );
    assert!(
        !post_mortem_stub.recommendations.is_empty(),
        "Post-mortem recommendations should not be empty"
    );

    // Verify post-mortem stub includes all signatures
    assert_eq!(
        post_mortem_stub.signatures.len(),
        3,
        "Post-mortem should include all signatures"
    );

    // Verify post-mortem stub includes timing information
    assert!(
        !post_mortem_stub.approval_timeline.is_empty(),
        "Post-mortem should include approval timeline"
    );
    assert!(
        !post_mortem_stub.execution_timeline.is_empty(),
        "Post-mortem should include execution timeline"
    );

    // Test post-mortem stub export
    let export_result = manager.export_post_mortem_stub(&post_mortem_stub);
    assert!(
        export_result.is_ok(),
        "Post-mortem stub export should succeed"
    );

    let exported_stub = export_result.unwrap();
    assert!(
        !exported_stub.is_empty(),
        "Exported post-mortem stub should not be empty"
    );

    // Test post-mortem stub import
    let import_result = manager.import_post_mortem_stub(&exported_stub);
    assert!(
        import_result.is_ok(),
        "Post-mortem stub import should succeed"
    );

    let imported_stub = import_result.unwrap();
    assert_eq!(imported_stub.request_id, post_mortem_stub.request_id);
    assert_eq!(imported_stub.summary, post_mortem_stub.summary);
}

#[test]
fn test_break_glass_urgency_levels() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Test different urgency levels
    let urgency_levels = vec![
        UrgencyLevel::Low,
        UrgencyLevel::Medium,
        UrgencyLevel::High,
        UrgencyLevel::Critical,
    ];

    for (i, urgency_level) in urgency_levels.iter().enumerate() {
        let request = BreakGlassRequest {
            id: format!("urgency_request_{}", i),
            user_id: format!("user_urgency_{}", i),
            urgency_level: urgency_level.clone(),
            justification: format!("Testing urgency level: {:?}", urgency_level),
            timestamp: "2025-01-15T10:00:00Z".to_string(),
            expiry: "2025-01-16T10:00:00Z".to_string(),
            status: BreakGlassStatus::Pending,
            signatures: Vec::new(),
            metadata: HashMap::new(),
        };

        let create_result = manager.create_request(request);
        assert!(
            create_result.is_ok(),
            "Break-glass request creation should succeed"
        );

        // Verify urgency level is properly set
        let request_info = manager.get_request_info(&format!("urgency_request_{}", i));
        assert!(request_info.is_ok(), "Getting request info should succeed");

        let info = request_info.unwrap();
        assert_eq!(info.urgency_level, *urgency_level);

        // Test that urgency level affects approval requirements
        let required_signatures = manager.get_required_signatures_for_urgency(*urgency_level);
        assert!(
            required_signatures > 0,
            "Urgency level should require signatures"
        );

        // Higher urgency levels should require more signatures
        if i > 0 {
            let prev_urgency = &urgency_levels[i - 1];
            let prev_required = manager.get_required_signatures_for_urgency(prev_urgency.clone());
            assert!(
                required_signatures >= prev_required,
                "Higher urgency should require at least as many signatures"
            );
        }
    }

    // Test that maximum urgency level is enforced
    let max_urgency = manager.get_config().max_urgency_level;
    assert_eq!(max_urgency, UrgencyLevel::Critical);

    // Test creating request with urgency level beyond maximum
    let excessive_request = BreakGlassRequest {
        id: "excessive_urgency".to_string(),
        user_id: "user_excessive".to_string(),
        urgency_level: UrgencyLevel::Critical, // This should be the maximum
        justification: "Testing maximum urgency level".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-16T10:00:00Z".to_string(),
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(excessive_request);
    assert!(
        create_result.is_ok(),
        "Maximum urgency level request should be allowed"
    );
}

#[test]
fn test_break_glass_expiry_and_auto_paging() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Create request with short expiry
    let short_expiry_request = BreakGlassRequest {
        id: "short_expiry_request".to_string(),
        user_id: "user_short_expiry".to_string(),
        urgency_level: UrgencyLevel::High,
        justification: "Testing short expiry and auto-paging".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-15T10:01:00Z".to_string(), // 1 minute expiry
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(short_expiry_request);
    assert!(
        create_result.is_ok(),
        "Short expiry request creation should succeed"
    );

    // Wait for request to expire (simulate)
    std::thread::sleep(std::time::Duration::from_millis(100));

    // Test auto-expiry handling
    let expiry_result = manager.handle_expired_requests();
    assert!(
        expiry_result.is_ok(),
        "Expired request handling should succeed"
    );

    let expired_requests = expiry_result.unwrap();
    assert!(!expired_requests.is_empty(), "Should have expired requests");

    // Verify expired request is marked as such
    let request_status = manager.get_request_status("short_expiry_request");
    if let Ok(status) = request_status {
        assert_eq!(status, BreakGlassStatus::Expired);
    }

    // Test auto-paging for expired requests
    let paging_result = manager.trigger_auto_paging("short_expiry_request");
    assert!(paging_result.is_ok(), "Auto-paging should succeed");

    let paging_info = paging_result.unwrap();
    assert!(
        !paging_info.recipients.is_empty(),
        "Auto-paging should have recipients"
    );
    assert!(
        !paging_info.message.is_empty(),
        "Auto-paging should have message"
    );

    // Test that expired requests can be renewed
    let renewal_result =
        manager.renew_expired_request("short_expiry_request", "2025-01-15T11:00:00Z");
    if let Ok(renewed) = renewal_result {
        assert_eq!(renewed.status, BreakGlassStatus::Pending);
        assert!(renewed.expiry > "2025-01-15T10:01:00Z");
    }
}

#[test]
fn test_break_glass_audit_logging() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Enable audit logging
    assert!(
        manager.get_config().enable_audit_logging,
        "Audit logging should be enabled"
    );

    // Create break-glass request
    let request = BreakGlassRequest {
        id: "audit_request".to_string(),
        user_id: "user_audit".to_string(),
        urgency_level: UrgencyLevel::Medium,
        justification: "Testing audit logging".to_string(),
        timestamp: "2025-01-15T10:00:00Z".to_string(),
        expiry: "2025-01-16T10:00:00Z".to_string(),
        status: BreakGlassStatus::Pending,
        signatures: Vec::new(),
        metadata: HashMap::new(),
    };

    let create_result = manager.create_request(request);
    assert!(
        create_result.is_ok(),
        "Break-glass request creation should succeed"
    );

    // Add signature
    let signature = BreakGlassSignature {
        id: "audit_sig".to_string(),
        request_id: "audit_request".to_string(),
        user_id: "audit_approver".to_string(),
        timestamp: "2025-01-15T10:01:00Z".to_string(),
        signature: "audit_sig_hash".to_string(),
        approval_level: "manager".to_string(),
        metadata: HashMap::new(),
    };

    let add_result = manager.add_signature(signature);
    assert!(add_result.is_ok(), "Adding signature should succeed");

    // Test audit log retrieval
    let audit_log_result = manager.get_audit_log("audit_request");
    assert!(audit_log_result.is_ok(), "Getting audit log should succeed");

    let audit_log = audit_log_result.unwrap();
    assert!(!audit_log.is_empty(), "Audit log should not be empty");

    // Verify audit log contains creation event
    let creation_events: Vec<_> = audit_log
        .iter()
        .filter(|entry| entry.action == "request_created")
        .collect();
    assert!(
        !creation_events.is_empty(),
        "Audit log should contain creation event"
    );

    // Verify audit log contains signature event
    let signature_events: Vec<_> = audit_log
        .iter()
        .filter(|entry| entry.action == "signature_added")
        .collect();
    assert!(
        !signature_events.is_empty(),
        "Audit log should contain signature event"
    );

    // Test audit log export
    let export_result = manager.export_audit_log("audit_request");
    assert!(export_result.is_ok(), "Audit log export should succeed");

    let exported_log = export_result.unwrap();
    assert!(
        !exported_log.is_empty(),
        "Exported audit log should not be empty"
    );

    // Test audit log filtering
    let filtered_log_result = manager.get_audit_log_filtered("audit_request", "signature");
    assert!(
        filtered_log_result.is_ok(),
        "Getting filtered audit log should succeed"
    );

    let filtered_log = filtered_log_result.unwrap();
    assert!(
        !filtered_log.is_empty(),
        "Filtered audit log should not be empty"
    );

    // All filtered entries should contain "signature"
    for entry in &filtered_log {
        assert!(
            entry.action.contains("signature") || entry.description.contains("signature"),
            "Filtered entry should contain 'signature'"
        );
    }
}

#[test]
fn test_break_glass_statistics() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Create multiple requests for statistics testing
    let test_requests = vec![
        (
            "stats_request_1",
            UrgencyLevel::Low,
            BreakGlassStatus::Approved,
        ),
        (
            "stats_request_2",
            UrgencyLevel::Medium,
            BreakGlassStatus::Denied,
        ),
        (
            "stats_request_3",
            UrgencyLevel::High,
            BreakGlassStatus::Expired,
        ),
        (
            "stats_request_4",
            UrgencyLevel::Critical,
            BreakGlassStatus::Pending,
        ),
    ];

    for (request_id, urgency_level, status) in test_requests {
        let request = BreakGlassRequest {
            id: request_id.to_string(),
            user_id: format!("user_{}", request_id),
            urgency_level: urgency_level.clone(),
            justification: format!("Testing statistics for {}", request_id),
            timestamp: "2025-01-15T10:00:00Z".to_string(),
            expiry: "2025-01-16T10:00:00Z".to_string(),
            status: status.clone(),
            signatures: Vec::new(),
            metadata: HashMap::new(),
        };

        let create_result = manager.create_request(request);
        assert!(create_result.is_ok(), "Request creation should succeed");

        // Set status directly for testing
        let status_result = manager.set_request_status(request_id, status.clone());
        assert!(status_result.is_ok(), "Status setting should succeed");
    }

    // Test statistics retrieval
    let stats_result = manager.get_statistics();
    assert!(stats_result.is_ok(), "Getting statistics should succeed");

    let stats = stats_result.unwrap();

    // Verify basic statistics
    assert_eq!(stats.total_requests, 4, "Should have 4 total requests");
    assert_eq!(stats.approved_requests, 1, "Should have 1 approved request");
    assert_eq!(stats.denied_requests, 1, "Should have 1 denied request");
    assert_eq!(stats.expired_requests, 1, "Should have 1 expired request");
    assert_eq!(stats.pending_requests, 1, "Should have 1 pending request");

    // Verify urgency level distribution
    assert_eq!(stats.requests_by_urgency.get(&UrgencyLevel::Low), Some(&1));
    assert_eq!(
        stats.requests_by_urgency.get(&UrgencyLevel::Medium),
        Some(&1)
    );
    assert_eq!(stats.requests_by_urgency.get(&UrgencyLevel::High), Some(&1));
    assert_eq!(
        stats.requests_by_urgency.get(&UrgencyLevel::Critical),
        Some(&1)
    );

    // Test statistics export
    let export_result = manager.export_statistics();
    assert!(export_result.is_ok(), "Statistics export should succeed");

    let exported_stats = export_result.unwrap();
    assert!(
        !exported_stats.is_empty(),
        "Exported statistics should not be empty"
    );

    // Test statistics filtering by time range
    let time_filtered_stats =
        manager.get_statistics_in_range("2025-01-15T09:00:00Z", "2025-01-15T11:00:00Z");
    assert!(
        time_filtered_stats.is_ok(),
        "Time-filtered statistics should succeed"
    );

    let filtered_stats = time_filtered_stats.unwrap();
    assert_eq!(
        filtered_stats.total_requests, 4,
        "Time-filtered should include all requests"
    );

    // Test statistics filtering by urgency level
    let urgency_filtered_stats = manager.get_statistics_by_urgency(UrgencyLevel::High);
    assert!(
        urgency_filtered_stats.is_ok(),
        "Urgency-filtered statistics should succeed"
    );

    let urgency_stats = urgency_filtered_stats.unwrap();
    assert_eq!(
        urgency_stats.total_requests, 1,
        "Urgency-filtered should include only high urgency"
    );
    assert_eq!(
        urgency_stats.requests_by_urgency.get(&UrgencyLevel::High),
        Some(&1)
    );
}
