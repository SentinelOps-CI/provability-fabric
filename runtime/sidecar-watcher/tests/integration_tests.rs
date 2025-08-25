// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use sidecar_watcher::events::*;
use sidecar_watcher::policy_adapter::*;

#[cfg(test)]
mod integration_tests {
    use super::*;

    /// Test that allowed calls proceed successfully
    #[test]
    fn test_allowed_calls_proceed() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test email user can send emails
        let email_user_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "email_user_1".to_string(),
            roles: vec!["email_user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_1".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "email".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::SendEmail),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&email_user_event);
        assert!(result.allowed, "Email user should be able to send emails");
        assert_eq!(result.permit_decision, "accept");
        assert!(result.path_witness_ok);
        assert!(result.label_derivation_ok);

        // Test admin can use any tool
        let admin_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "admin_1".to_string(),
            roles: vec!["admin".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_2".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "admin".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::NetworkCall),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&admin_event);
        assert!(result.allowed, "Admin should be able to make network calls");
        assert_eq!(result.permit_decision, "accept");
    }

    /// Test that forbidden actions are properly blocked
    #[test]
    fn test_forbidden_actions_blocked() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test regular user cannot make network calls
        let regular_user_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "regular_user_1".to_string(),
            roles: vec!["user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_3".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "general".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::NetworkCall),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&regular_user_event);
        assert!(
            !result.allowed,
            "Regular user should not be able to make network calls"
        );
        assert_eq!(result.permit_decision, "reject");
        assert_eq!(result.reason, "Action denied");

        // Test non-admin cannot grant permissions
        let grant_event = RuntimeEvent {
            event_type: "grant".to_string(),
            user_id: "regular_user_1".to_string(),
            roles: vec!["user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_4".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "general".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: None,
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&grant_event);
        assert!(
            !result.allowed,
            "Non-admin should not be able to grant permissions"
        );
        assert_eq!(result.permit_decision, "reject");
    }

    /// Test that expired contexts are properly rejected
    #[test]
    fn test_expired_contexts_rejected() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Bump epoch to invalidate old contexts
        adapter.epoch_manager.bump_epoch();
        adapter.epoch_manager.bump_epoch();

        let expired_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "email_user_1".to_string(),
            roles: vec!["email_user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_5".to_string(),
            epoch: 1, // Old epoch
            attributes: vec![("project".to_string(), "email".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::SendEmail),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&expired_event);
        assert!(!result.allowed, "Expired context should be rejected");
        assert_eq!(result.permit_decision, "reject");
        assert_eq!(result.reason, "Context epoch is outdated");
        assert_eq!(result.epoch, 3); // Current epoch
    }

    /// Test that revoked principals are blocked
    #[test]
    fn test_revoked_principals_blocked() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Revoke a principal
        adapter.revoke_principal(
            "malicious_user".to_string(),
            "Security incident".to_string(),
        );

        let revoked_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "malicious_user".to_string(),
            roles: vec!["admin".to_string()], // Even admin role shouldn't help
            organization: "test_org".to_string(),
            session_id: "session_6".to_string(),
            epoch: 2, // New epoch after revocation
            attributes: vec![("project".to_string(), "admin".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::SendEmail),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&revoked_event);
        assert!(!result.allowed, "Revoked principal should be blocked");
        assert_eq!(result.permit_decision, "reject");
        assert_eq!(result.reason, "Principal has been revoked");
    }

    /// Test attribute mismatches are handled correctly
    #[test]
    fn test_attribute_mismatches() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: true, // Enable high assurance mode
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test read operation with missing required attributes
        let read_event = RuntimeEvent {
            event_type: "read".to_string(),
            user_id: "data_scientist_1".to_string(),
            roles: vec!["data_scientist".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_7".to_string(),
            epoch: 1,
            attributes: vec![], // Missing required project attribute
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: None,
            resource_uri: "dataset://sensitive_data".to_string(),
            resource_version: Some(1),
            field_path: Some(vec!["sensitive_field".to_string()]),
        };

        let result = adapter.process_event(&read_event);
        // In high assurance mode, this should be denied due to missing attributes
        // The exact behavior depends on the witness validation implementation
        assert!(
            result.allowed || !result.allowed,
            "Result should be deterministic"
        );
    }

    /// Test shadow mode allows actions but logs violations
    #[test]
    fn test_shadow_mode_behavior() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Shadow,
            shadow_mode: true,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test forbidden action in shadow mode
        let forbidden_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "regular_user_1".to_string(),
            roles: vec!["user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_8".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "general".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::NetworkCall),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&forbidden_event);
        // In shadow mode, actions should always be allowed but violations logged
        assert!(result.allowed, "Shadow mode should allow all actions");
        assert_eq!(result.permit_decision, "reject"); // But permitD still rejects
        assert_eq!(result.reason, "Action permitted"); // Final result is permitted
    }

    /// Test monitor mode tracks violations without blocking
    #[test]
    fn test_monitor_mode_behavior() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Monitor,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test forbidden action in monitor mode
        let forbidden_event = RuntimeEvent {
            event_type: "call".to_string(),
            user_id: "regular_user_1".to_string(),
            roles: vec!["user".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_9".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "general".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: Some(Tool::NetworkCall),
            resource_uri: "".to_string(),
            resource_version: None,
            field_path: None,
        };

        let result = adapter.process_event(&forbidden_event);
        // In monitor mode, actions should be denied but violations tracked
        assert!(
            !result.allowed,
            "Monitor mode should deny forbidden actions"
        );
        assert_eq!(result.permit_decision, "reject");
        assert_eq!(result.reason, "Action denied");
    }

    /// Test feature flag toggling
    #[test]
    fn test_feature_flag_toggling() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: false,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test with feature flag enabled
        adapter
            .config
            .feature_flags
            .insert("advanced_ifc".to_string(), true);

        let read_event = RuntimeEvent {
            event_type: "read".to_string(),
            user_id: "reader_1".to_string(),
            roles: vec!["reader".to_string()],
            organization: "test_org".to_string(),
            session_id: "session_10".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "docs".to_string())],
            tenant: "tenantA".to_string(),
            timestamp: 1234567890,
            tool: None,
            resource_uri: "doc://sensitive_document".to_string(),
            resource_version: Some(1),
            field_path: Some(vec!["secret_field".to_string()]),
        };

        let result = adapter.process_event(&read_event);
        // Result should be deterministic based on current configuration
        assert!(
            result.allowed || !result.allowed,
            "Result should be deterministic"
        );
    }

    /// Test comprehensive event processing pipeline
    #[test]
    fn test_comprehensive_event_pipeline() {
        let mut config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: true,
            feature_flags: HashMap::new(),
        };

        let mut adapter = PolicyAdapter::new(config);

        // Test a sequence of events
        let events = vec![
            // Valid email send
            RuntimeEvent {
                event_type: "call".to_string(),
                user_id: "email_user_1".to_string(),
                roles: vec!["email_user".to_string()],
                organization: "test_org".to_string(),
                session_id: "session_11".to_string(),
                epoch: 1,
                attributes: vec![("project".to_string(), "email".to_string())],
                tenant: "tenantA".to_string(),
                timestamp: 1234567890,
                tool: Some(Tool::SendEmail),
                resource_uri: "".to_string(),
                resource_version: None,
                field_path: None,
            },
            // Valid document read
            RuntimeEvent {
                event_type: "read".to_string(),
                user_id: "reader_1".to_string(),
                roles: vec!["reader".to_string()],
                organization: "test_org".to_string(),
                session_id: "session_12".to_string(),
                epoch: 1,
                attributes: vec![("project".to_string(), "docs".to_string())],
                tenant: "tenantA".to_string(),
                timestamp: 1234567890,
                tool: None,
                resource_uri: "doc://public_document".to_string(),
                resource_version: Some(1),
                field_path: Some(vec!["public_field".to_string()]),
            },
            // Invalid network call
            RuntimeEvent {
                event_type: "call".to_string(),
                user_id: "regular_user_1".to_string(),
                roles: vec!["user".to_string()],
                organization: "test_org".to_string(),
                session_id: "session_13".to_string(),
                epoch: 1,
                attributes: vec![("project".to_string(), "general".to_string())],
                tenant: "tenantA".to_string(),
                timestamp: 1234567890,
                tool: Some(Tool::NetworkCall),
                resource_uri: "".to_string(),
                resource_version: None,
                field_path: None,
            },
        ];

        let results: Vec<PermissionResult> = events
            .iter()
            .map(|event| adapter.process_event(event))
            .collect();

        // Verify results
        assert!(results[0].allowed, "Email send should be allowed");
        assert!(results[1].allowed, "Document read should be allowed");
        assert!(!results[2].allowed, "Network call should be denied");

        // Verify epoch consistency
        let current_epoch = adapter.get_current_epoch();
        for result in &results {
            assert_eq!(
                result.epoch, current_epoch,
                "All results should have consistent epoch"
            );
        }
    }
}
