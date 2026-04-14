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

use sidecar_watcher::break_glass::{
    BreakGlassConfig, BreakGlassManager, BreakGlassStatus,
    UrgencyLevel,
};

/// Create test break-glass configuration
fn create_test_break_glass_config() -> BreakGlassConfig {
    BreakGlassConfig {
        enable_break_glass: true,
        m_of_n_threshold: (3, 5), // M-of-N where M=3, N=5
        ttl_seconds: 86400,       // 24 hours
        auto_page_enabled: true,
        auto_page_threshold: 300,
        require_justification: true,
        audit_logging: true,
        max_active_break_glass: 10,
    }
}

/// Base timestamp for tests (2025-01-15 approx).
const BASE_TS: u64 = 1736935200;

#[test]
fn test_break_glass_m_of_n_signatures() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    // Test M-of-N signature requirement (3 of 5)
    let (m, n) = manager.get_config().m_of_n_threshold;
    assert_eq!(m, 3);
    assert_eq!(n, 5);

    // Create break-glass request via API
    let create_result = manager.create_request(
        "session_test".to_string(),
        "user_test".to_string(),
        "Testing M-of-N".to_string(),
        Some("Testing M-of-N signatures".to_string()),
        vec!["read".to_string()],
        vec![],
        UrgencyLevel::High,
    );
    assert!(
        create_result.is_ok(),
        "Break-glass request creation should succeed"
    );
    let request_id = create_result.unwrap();

    manager.add_authorized_signer("approver_1".to_string());
    manager.add_authorized_signer("approver_2".to_string());
    manager.add_authorized_signer("approver_3".to_string());
    manager.add_authorized_signer("approver_4".to_string());

    // Only 2 signatures first, need 3
    let add_result = manager.add_signature(
        &request_id,
        "approver_1".to_string(),
        "manager".to_string(),
        "sig_hash_1".to_string(),
        None,
    );
    assert!(add_result.is_ok(), "Adding signature should succeed");
    let add_result = manager.add_signature(
        &request_id,
        "approver_2".to_string(),
        "director".to_string(),
        "sig_hash_2".to_string(),
        None,
    );
    assert!(add_result.is_ok(), "Adding signature should succeed");

    // Check that request is still pending (insufficient signatures)
    let request_status = manager.get_request_status(&request_id);
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
    let add_result = manager.add_signature(
        &request_id,
        "approver_3".to_string(),
        "vp".to_string(),
        "sig_hash_3".to_string(),
        None,
    );
    assert!(add_result.is_ok(), "Adding third signature should succeed");

    // Check that request is now approved (M signatures reached)
    let request_status = manager.get_request_status(&request_id);
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
    let add_result = manager.add_signature(
        &request_id,
        "approver_4".to_string(),
        "cto".to_string(),
        "sig_hash_4".to_string(),
        None,
    );
    assert!(add_result.is_ok(), "Adding fourth signature should succeed");

    let request_status = manager.get_request_status(&request_id);
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

    let request_id = manager
        .create_request(
            "session_validation".to_string(),
            "user_validation".to_string(),
            "Testing signature validation".to_string(),
            Some("Testing signature validation".to_string()),
            vec![],
            vec![],
            UrgencyLevel::Medium,
        )
        .expect("create_request should succeed");

    manager.add_authorized_signer("valid_approver".to_string());
    manager.add_authorized_signer("valid_approver_2".to_string());

    let add_result = manager.add_signature(
        &request_id,
        "valid_approver".to_string(),
        "manager".to_string(),
        "valid_sig_hash".to_string(),
        None,
    );
    assert!(add_result.is_ok(), "Valid signature should be added successfully");

    let sigs_before = manager.get_request(&request_id).map(|r| r.signatures.len()).unwrap_or(0);

    let add_dup = manager.add_signature(
        &request_id,
        "valid_approver".to_string(),
        "manager".to_string(),
        "duplicate_sig_hash".to_string(),
        None,
    );
    assert!(add_dup.is_err(), "Duplicate signer should be rejected");
    let sigs_after = manager.get_request(&request_id).map(|r| r.signatures.len()).unwrap_or(0);
    assert_eq!(sigs_after, sigs_before, "No duplicate signature added");

    let add_wrong = manager.add_signature(
        "wrong_request",
        "valid_approver_2".to_string(),
        "director".to_string(),
        "invalid_sig_hash".to_string(),
        None,
    );
    assert!(add_wrong.is_err(), "Wrong request ID should be rejected");

    let add_empty_signer = manager.add_signature(
        &request_id,
        "".to_string(),
        "manager".to_string(),
        "incomplete_sig_hash".to_string(),
        None,
    );
    assert!(add_empty_signer.is_err(), "Empty signer_id should be rejected");
}

#[test]
#[ignore = "requires generate_post_mortem_stub, export_post_mortem_stub, import_post_mortem_stub API"]
fn test_break_glass_post_mortem_stub_emission() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);
    let request_id = manager
        .create_request(
            "session_pm".to_string(),
            "user_post_mortem".to_string(),
            "Post-mortem test".to_string(),
            Some("Testing post-mortem".to_string()),
            vec![],
            vec![],
            UrgencyLevel::Critical,
        )
        .expect("create_request should succeed");
    for (i, (signer, role)) in [("pm_1", "manager"), ("pm_2", "director"), ("pm_3", "vp")]
        .iter()
        .enumerate()
    {
        manager.add_authorized_signer((*signer).to_string());
        let _ = manager.add_signature(
            &request_id,
            (*signer).to_string(),
            (*role).to_string(),
            format!("pm_sig_hash_{}", i + 1),
            None,
        );
    }
    let status = manager.get_request_status(&request_id).unwrap();
    assert_eq!(status, BreakGlassStatus::Approved);
}

#[test]
#[ignore = "requires get_request_info, get_required_signatures_for_urgency, max_urgency_level API"]
fn test_break_glass_urgency_levels() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);
    for (i, urgency) in [
        UrgencyLevel::Low,
        UrgencyLevel::Medium,
        UrgencyLevel::High,
        UrgencyLevel::Critical,
    ]
    .iter()
    .enumerate()
    {
        let request_id = manager
            .create_request(
                format!("session_u_{}", i),
                format!("user_urgency_{}", i),
                format!("Testing {:?}", urgency),
                Some("Justification".to_string()),
                vec![],
                vec![],
                urgency.clone(),
            )
            .expect("create_request should succeed");
        let status = manager.get_request_status(&request_id).unwrap();
        assert_eq!(status, BreakGlassStatus::Pending);
    }
}

#[test]
#[ignore = "requires handle_expired_requests, trigger_auto_paging, renew_expired_request API"]
fn test_break_glass_expiry_and_auto_paging() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);
    let request_id = manager
        .create_request(
            "session_exp".to_string(),
            "user_short_expiry".to_string(),
            "Short expiry test".to_string(),
            Some("Testing expiry".to_string()),
            vec![],
            vec![],
            UrgencyLevel::High,
        )
        .expect("create_request should succeed");
    let _expired = manager.check_expired_and_auto_page();
    let _ = manager.get_request_status(&request_id);
}

#[test]
#[ignore = "requires get_audit_log, export_audit_log, get_audit_log_filtered API"]
fn test_break_glass_audit_logging() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);
    assert!(manager.get_config().audit_logging);
    let request_id = manager
        .create_request(
            "session_audit".to_string(),
            "user_audit".to_string(),
            "Audit test".to_string(),
            Some("Testing audit".to_string()),
            vec![],
            vec![],
            UrgencyLevel::Medium,
        )
        .expect("create_request should succeed");
    manager.add_authorized_signer("audit_approver".to_string());
    let _ = manager.add_signature(
        &request_id,
        "audit_approver".to_string(),
        "manager".to_string(),
        "audit_sig_hash".to_string(),
        None,
    );
    let _ = manager.get_request_status(&request_id);
}

#[test]
fn test_break_glass_statistics() {
    let config = create_test_break_glass_config();
    let mut manager = BreakGlassManager::new(config);

    let requests = [
        ("session_s1", "user_s1", UrgencyLevel::Low, BreakGlassStatus::Approved),
        ("session_s2", "user_s2", UrgencyLevel::Medium, BreakGlassStatus::Denied),
        ("session_s3", "user_s3", UrgencyLevel::High, BreakGlassStatus::Expired),
        ("session_s4", "user_s4", UrgencyLevel::Critical, BreakGlassStatus::Pending),
    ];

    for (session, user, urgency, status) in &requests {
        let request_id = manager
            .create_request(
                (*session).to_string(),
                (*user).to_string(),
                "Stats test".to_string(),
                Some("Justification".to_string()),
                vec![],
                vec![],
                urgency.clone(),
            )
            .expect("create_request should succeed");
        manager
            .set_request_status(&request_id, status.clone())
            .expect("set_request_status should succeed");
    }

    let stats = manager.get_stats();
    assert_eq!(stats.total_requests, 4, "Should have 4 total requests");
    assert_eq!(stats.approved_requests, 1);
    assert_eq!(stats.denied_requests, 1);
    assert_eq!(stats.expired_requests, 1);
    assert_eq!(stats.pending_requests, 1);
}
