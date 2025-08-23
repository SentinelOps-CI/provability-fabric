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

use serde_json::json;
use sidecar_watcher::declassify::SecurityLabel;
use sidecar_watcher::events::{
    EventMediationResult, EventMediator, EventType, FieldCommitment, MediationError, OperationArgs,
    PlanNode, TypedEvent,
};
use std::collections::HashMap;

/// Create a comprehensive set of plan nodes for testing
fn create_test_plan_nodes() -> Vec<PlanNode> {
    vec![
        PlanNode {
            id: "user_login".to_string(),
            operation: "call".to_string(),
            target: "auth_service".to_string(),
            field_commit: Some(FieldCommitment {
                fields: vec!["user_id".to_string(), "timestamp".to_string()],
                hash: "commit_hash_user_login".to_string(),
            }),
            args_hash: Some("args_hash_user_login_123".to_string()),
            security_label: SecurityLabel::Confidential,
            declass_rules: vec!["rule_1".to_string()],
        },
        PlanNode {
            id: "data_export".to_string(),
            operation: "emit".to_string(),
            target: "export_service".to_string(),
            field_commit: Some(FieldCommitment {
                fields: vec![
                    "data_type".to_string(),
                    "record_count".to_string(),
                    "checksum".to_string(),
                ],
                hash: "commit_hash_data_export".to_string(),
            }),
            args_hash: Some("args_hash_data_export_456".to_string()),
            security_label: SecurityLabel::Secret,
            declass_rules: vec!["rule_2".to_string(), "rule_3".to_string()],
        },
        PlanNode {
            id: "log_audit".to_string(),
            operation: "log".to_string(),
            target: "audit_log".to_string(),
            field_commit: Some(FieldCommitment {
                fields: vec![
                    "event_type".to_string(),
                    "user_id".to_string(),
                    "timestamp".to_string(),
                ],
                hash: "commit_hash_log_audit".to_string(),
            }),
            args_hash: Some("args_hash_log_audit_789".to_string()),
            security_label: SecurityLabel::Internal,
            declass_rules: vec![],
        },
        PlanNode {
            id: "declassify_user_info".to_string(),
            operation: "declassify".to_string(),
            target: "user_service".to_string(),
            field_commit: Some(FieldCommitment {
                fields: vec!["user_id".to_string(), "declass_level".to_string()],
                hash: "commit_hash_declassify_user_info".to_string(),
            }),
            args_hash: Some("args_hash_declassify_user_info_abc".to_string()),
            security_label: SecurityLabel::Secret,
            declass_rules: vec!["rule_4".to_string()],
        },
        PlanNode {
            id: "retrieve_config".to_string(),
            operation: "retrieve".to_string(),
            target: "config_service".to_string(),
            field_commit: Some(FieldCommitment {
                fields: vec!["config_key".to_string(), "version".to_string()],
                hash: "commit_hash_retrieve_config".to_string(),
            }),
            args_hash: Some("args_hash_retrieve_config_def".to_string()),
            security_label: SecurityLabel::Internal,
            declass_rules: vec![],
        },
    ]
}

/// Create test events with various field commitments and argument hashes
fn create_test_events() -> Vec<TypedEvent> {
    vec![
        TypedEvent {
            event_type: EventType::Call,
            target: "auth_service".to_string(),
            operation_args: OperationArgs {
                user_id: "user123".to_string(),
                timestamp: "2025-01-15T10:30:00Z".to_string(),
                password: "hashed_password_123".to_string(),
                session_id: "session_abc".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec!["user_id".to_string(), "timestamp".to_string()],
                hash: "commit_hash_user_login".to_string(),
            }),
            args_hash: Some("args_hash_user_login_123".to_string()),
            security_label: SecurityLabel::Confidential,
        },
        TypedEvent {
            event_type: EventType::Emit,
            target: "export_service".to_string(),
            operation_args: OperationArgs {
                data_type: "user_records".to_string(),
                record_count: "1000".to_string(),
                checksum: "sha256_checksum_abc".to_string(),
                export_format: "json".to_string(),
                compression: "gzip".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec![
                    "data_type".to_string(),
                    "record_count".to_string(),
                    "checksum".to_string(),
                ],
                hash: "commit_hash_data_export".to_string(),
            }),
            args_hash: Some("args_hash_data_export_456".to_string()),
            security_label: SecurityLabel::Secret,
        },
        TypedEvent {
            event_type: EventType::Log,
            target: "audit_log".to_string(),
            operation_args: OperationArgs {
                event_type: "user_login".to_string(),
                user_id: "user123".to_string(),
                timestamp: "2025-01-15T10:30:00Z".to_string(),
                ip_address: "192.168.1.100".to_string(),
                user_agent: "Mozilla/5.0".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec![
                    "event_type".to_string(),
                    "user_id".to_string(),
                    "timestamp".to_string(),
                ],
                hash: "commit_hash_log_audit".to_string(),
            }),
            args_hash: Some("args_hash_log_audit_789".to_string()),
            security_label: SecurityLabel::Internal,
        },
        TypedEvent {
            event_type: EventType::Declassify,
            target: "user_service".to_string(),
            operation_args: OperationArgs {
                user_id: "user123".to_string(),
                declass_level: "confidential".to_string(),
                justification: "Business need".to_string(),
                approver: "manager_456".to_string(),
                expiry: "2025-02-15T10:30:00Z".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec!["user_id".to_string(), "declass_level".to_string()],
                hash: "commit_hash_declassify_user_info".to_string(),
            }),
            args_hash: Some("args_hash_declassify_user_info_abc".to_string()),
            security_label: SecurityLabel::Secret,
        },
        TypedEvent {
            event_type: EventType::Retrieve,
            target: "config_service".to_string(),
            operation_args: OperationArgs {
                config_key: "database_connection".to_string(),
                version: "v2.1".to_string(),
                environment: "production".to_string(),
                cache_ttl: "300".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec!["config_key".to_string(), "version".to_string()],
                hash: "commit_hash_retrieve_config".to_string(),
            }),
            args_hash: Some("args_hash_retrieve_config_def".to_string()),
            security_label: SecurityLabel::Internal,
        },
    ]
}

/// Create events with missing field commitments
fn create_events_missing_commitments() -> Vec<TypedEvent> {
    vec![
        TypedEvent {
            event_type: EventType::Call,
            target: "auth_service".to_string(),
            operation_args: OperationArgs {
                user_id: "user123".to_string(),
                timestamp: "2025-01-15T10:30:00Z".to_string(),
                password: "hashed_password_123".to_string(),
                session_id: "session_abc".to_string(),
            },
            field_commit: None, // Missing field commitment
            args_hash: Some("args_hash_user_login_123".to_string()),
            security_label: SecurityLabel::Confidential,
        },
        TypedEvent {
            event_type: EventType::Emit,
            target: "export_service".to_string(),
            operation_args: OperationArgs {
                data_type: "user_records".to_string(),
                record_count: "1000".to_string(),
                checksum: "sha256_checksum_abc".to_string(),
                export_format: "json".to_string(),
                compression: "gzip".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec!["data_type".to_string(), "record_count".to_string()], // Missing checksum
                hash: "commit_hash_data_export".to_string(),
            }),
            args_hash: Some("args_hash_data_export_456".to_string()),
            security_label: SecurityLabel::Secret,
        },
    ]
}

/// Create events with hash mismatches
fn create_events_hash_mismatches() -> Vec<TypedEvent> {
    vec![
        TypedEvent {
            event_type: EventType::Call,
            target: "auth_service".to_string(),
            operation_args: OperationArgs {
                user_id: "user123".to_string(),
                timestamp: "2025-01-15T10:30:00Z".to_string(),
                password: "hashed_password_123".to_string(),
                session_id: "session_abc".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec!["user_id".to_string(), "timestamp".to_string()],
                hash: "commit_hash_user_login".to_string(),
            }),
            args_hash: Some("wrong_args_hash".to_string()), // Hash mismatch
            security_label: SecurityLabel::Confidential,
        },
        TypedEvent {
            event_type: EventType::Emit,
            target: "export_service".to_string(),
            operation_args: OperationArgs {
                data_type: "user_records".to_string(),
                record_count: "1000".to_string(),
                checksum: "sha256_checksum_abc".to_string(),
                export_format: "json".to_string(),
                compression: "gzip".to_string(),
            },
            field_commit: Some(FieldCommitment {
                fields: vec![
                    "data_type".to_string(),
                    "record_count".to_string(),
                    "checksum".to_string(),
                ],
                hash: "wrong_commit_hash".to_string(), // Hash mismatch
            }),
            args_hash: Some("args_hash_data_export_456".to_string()),
            security_label: SecurityLabel::Secret,
        },
    ]
}

#[test]
fn test_event_mediation_success() {
    let plan_nodes = create_test_plan_nodes();
    let events = create_test_events();
    let mediator = EventMediator::new(plan_nodes);

    for (i, event) in events.iter().enumerate() {
        let result = mediator.mediate_event(event);
        assert!(result.is_ok(), "Event {} mediation failed: {:?}", i, result);

        let mediation_result = result.unwrap();
        assert_eq!(
            mediation_result.allowed, true,
            "Event {} should be allowed",
            i
        );
        assert!(
            mediation_result.matched_plan_node.is_some(),
            "Event {} should have matched plan node",
            i
        );

        let matched_node = mediation_result.matched_plan_node.unwrap();
        assert_eq!(
            matched_node.id,
            match event.event_type {
                EventType::Call => "user_login",
                EventType::Emit => "data_export",
                EventType::Log => "log_audit",
                EventType::Declassify => "declassify_user_info",
                EventType::Retrieve => "retrieve_config",
            }
        );
    }
}

#[test]
fn test_event_mediation_missing_field_commitments() {
    let plan_nodes = create_test_plan_nodes();
    let events = create_events_missing_commitments();
    let mediator = EventMediator::new(plan_nodes);

    for (i, event) in events.iter().enumerate() {
        let result = mediator.mediate_event(event);

        match result {
            Ok(mediation_result) => {
                // If the event has no field commitment, it should be rejected
                if event.field_commit.is_none() {
                    assert_eq!(
                        mediation_result.allowed, false,
                        "Event {} without field commitment should be rejected",
                        i
                    );
                    assert_eq!(
                        mediation_result.reason,
                        Some("Missing field commitment".to_string())
                    );
                } else {
                    // If field commitment is incomplete, it should also be rejected
                    let plan_node = plan_nodes
                        .iter()
                        .find(|n| {
                            n.id == match event.event_type {
                                EventType::Call => "user_login",
                                EventType::Emit => "data_export",
                                _ => "unknown",
                            }
                        })
                        .unwrap();

                    let required_fields = &plan_node.field_commit.as_ref().unwrap().fields;
                    let provided_fields = &event.field_commit.as_ref().unwrap().fields;

                    if provided_fields.len() < required_fields.len() {
                        assert_eq!(
                            mediation_result.allowed, false,
                            "Event {} with incomplete field commitment should be rejected",
                            i
                        );
                        assert_eq!(
                            mediation_result.reason,
                            Some("Incomplete field commitment".to_string())
                        );
                    }
                }
            }
            Err(MediationError::MissingFieldCommitment) => {
                // This is also acceptable - the mediator could reject events with missing commitments
                assert!(
                    event.field_commit.is_none() || {
                        let plan_node = plan_nodes
                            .iter()
                            .find(|n| {
                                n.id == match event.event_type {
                                    EventType::Call => "user_login",
                                    EventType::Emit => "data_export",
                                    _ => "unknown",
                                }
                            })
                            .unwrap();

                        let required_fields = &plan_node.field_commit.as_ref().unwrap().fields;
                        let provided_fields = &event.field_commit.as_ref().unwrap().fields;
                        provided_fields.len() < required_fields.len()
                    }
                );
            }
            Err(e) => {
                panic!("Unexpected error for event {}: {:?}", i, e);
            }
        }
    }
}

#[test]
fn test_event_mediation_hash_mismatches() {
    let plan_nodes = create_test_plan_nodes();
    let events = create_events_hash_mismatches();
    let mediator = EventMediator::new(plan_nodes);

    for (i, event) in events.iter().enumerate() {
        let result = mediator.mediate_event(event);

        match result {
            Ok(mediation_result) => {
                // Events with hash mismatches should be rejected
                assert_eq!(
                    mediation_result.allowed, false,
                    "Event {} with hash mismatch should be rejected",
                    i
                );
                assert!(
                    mediation_result.reason.is_some(),
                    "Event {} should have rejection reason",
                    i
                );

                let reason = mediation_result.reason.unwrap();
                assert!(
                    reason.contains("hash") || reason.contains("mismatch"),
                    "Rejection reason should mention hash mismatch: {}",
                    reason
                );
            }
            Err(MediationError::HashMismatch { expected, actual }) => {
                // This is also acceptable - the mediator could reject events with hash mismatches
                assert_ne!(
                    expected, actual,
                    "Expected and actual hashes should be different for event {}",
                    i
                );
            }
            Err(e) => {
                panic!("Unexpected error for event {}: {:?}", i, e);
            }
        }
    }
}

#[test]
fn test_event_mediation_no_matching_plan_node() {
    let plan_nodes = create_test_plan_nodes();
    let mediator = EventMediator::new(plan_nodes);

    // Create an event that doesn't match any plan node
    let unmatched_event = TypedEvent {
        event_type: EventType::Call,
        target: "unknown_service".to_string(),
        operation_args: OperationArgs {
            user_id: "user123".to_string(),
            timestamp: "2025-01-15T10:30:00Z".to_string(),
            password: "hashed_password_123".to_string(),
            session_id: "session_abc".to_string(),
        },
        field_commit: Some(FieldCommitment {
            fields: vec!["user_id".to_string(), "timestamp".to_string()],
            hash: "commit_hash_unknown".to_string(),
        }),
        args_hash: Some("args_hash_unknown_123".to_string()),
        security_label: SecurityLabel::Confidential,
    };

    let result = mediator.mediate_event(&unmatched_event);

    match result {
        Ok(mediation_result) => {
            // The event should be rejected due to no matching plan node
            assert_eq!(
                mediation_result.allowed, false,
                "Unmatched event should be rejected"
            );
            assert_eq!(
                mediation_result.reason,
                Some("No matching plan node found".to_string())
            );
            assert!(
                mediation_result.matched_plan_node.is_none(),
                "Unmatched event should have no matched plan node"
            );
        }
        Err(MediationError::NoMatchingPlanNode) => {
            // This is also acceptable - the mediator could reject unmatched events
        }
        Err(e) => {
            panic!("Unexpected error for unmatched event: {:?}", e);
        }
    }
}

#[test]
fn test_event_mediation_security_label_escalation() {
    let plan_nodes = create_test_plan_nodes();
    let mediator = EventMediator::new(plan_nodes);

    // Create an event with a higher security label than the plan node allows
    let escalated_event = TypedEvent {
        event_type: EventType::Call,
        target: "auth_service".to_string(),
        operation_args: OperationArgs {
            user_id: "user123".to_string(),
            timestamp: "2025-01-15T10:30:00Z".to_string(),
            password: "hashed_password_123".to_string(),
            session_id: "session_abc".to_string(),
        },
        field_commit: Some(FieldCommitment {
            fields: vec!["user_id".to_string(), "timestamp".to_string()],
            hash: "commit_hash_user_login".to_string(),
        }),
        args_hash: Some("args_hash_user_login_123".to_string()),
        security_label: SecurityLabel::Secret, // Higher than plan node's Confidential
    };

    let result = mediator.mediate_event(&escalated_event);

    match result {
        Ok(mediation_result) => {
            // The event should be rejected due to security label escalation
            assert_eq!(
                mediation_result.allowed, false,
                "Security label escalated event should be rejected"
            );
            assert_eq!(
                mediation_result.reason,
                Some("Security label escalation not allowed".to_string())
            );
        }
        Err(MediationError::SecurityLabelEscalation { current, allowed }) => {
            // This is also acceptable - the mediator could reject escalated events
            assert_eq!(current, SecurityLabel::Secret);
            assert_eq!(allowed, SecurityLabel::Confidential);
        }
        Err(e) => {
            panic!(
                "Unexpected error for security label escalated event: {:?}",
                e
            );
        }
    }
}

#[test]
fn test_event_mediation_field_commitment_validation() {
    let plan_nodes = create_test_plan_nodes();
    let mediator = EventMediator::new(plan_nodes);

    // Test field commitment validation with various scenarios
    let test_cases = vec![
        // Valid field commitment
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec!["user_id".to_string(), "timestamp".to_string()],
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: Some("args_hash_user_login_123".to_string()),
                security_label: SecurityLabel::Confidential,
            },
            true, // Should be allowed
        ),
        // Missing required field
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec!["user_id".to_string()], // Missing timestamp
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: Some("args_hash_user_login_123".to_string()),
                security_label: SecurityLabel::Confidential,
            },
            false, // Should be rejected
        ),
        // Extra fields (should be allowed as long as required fields are present)
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec![
                        "user_id".to_string(),
                        "timestamp".to_string(),
                        "extra_field".to_string(),
                    ],
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: Some("args_hash_user_login_123".to_string()),
                security_label: SecurityLabel::Confidential,
            },
            true, // Should be allowed
        ),
    ];

    for (i, (event, expected_allowed)) in test_cases.iter().enumerate() {
        let result = mediator.mediate_event(event);

        match result {
            Ok(mediation_result) => {
                assert_eq!(
                    mediation_result.allowed, *expected_allowed,
                    "Test case {}: expected allowed={}, got allowed={}",
                    i, expected_allowed, mediation_result.allowed
                );

                if !expected_allowed {
                    assert!(
                        mediation_result.reason.is_some(),
                        "Test case {}: rejected event should have reason",
                        i
                    );
                }
            }
            Err(e) => {
                if *expected_allowed {
                    panic!("Test case {}: expected success but got error: {:?}", i, e);
                }
                // Error is acceptable for rejected events
            }
        }
    }
}

#[test]
fn test_event_mediation_args_hash_validation() {
    let plan_nodes = create_test_plan_nodes();
    let mediator = EventMediator::new(plan_nodes);

    // Test argument hash validation
    let test_cases = vec![
        // Valid args hash
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec!["user_id".to_string(), "timestamp".to_string()],
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: Some("args_hash_user_login_123".to_string()),
                security_label: SecurityLabel::Confidential,
            },
            true, // Should be allowed
        ),
        // Mismatched args hash
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec!["user_id".to_string(), "timestamp".to_string()],
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: Some("wrong_args_hash".to_string()),
                security_label: SecurityLabel::Confidential,
            },
            false, // Should be rejected
        ),
        // Missing args hash (should be rejected if plan node requires it)
        (
            TypedEvent {
                event_type: EventType::Call,
                target: "auth_service".to_string(),
                operation_args: OperationArgs {
                    user_id: "user123".to_string(),
                    timestamp: "2025-01-15T10:30:00Z".to_string(),
                    password: "hashed_password_123".to_string(),
                    session_id: "session_abc".to_string(),
                },
                field_commit: Some(FieldCommitment {
                    fields: vec!["user_id".to_string(), "timestamp".to_string()],
                    hash: "commit_hash_user_login".to_string(),
                }),
                args_hash: None,
                security_label: SecurityLabel::Confidential,
            },
            false, // Should be rejected
        ),
    ];

    for (i, (event, expected_allowed)) in test_cases.iter().enumerate() {
        let result = mediator.mediate_event(event);

        match result {
            Ok(mediation_result) => {
                assert_eq!(
                    mediation_result.allowed, *expected_allowed,
                    "Test case {}: expected allowed={}, got allowed={}",
                    i, expected_allowed, mediation_result.allowed
                );

                if !expected_allowed {
                    assert!(
                        mediation_result.reason.is_some(),
                        "Test case {}: rejected event should have reason",
                        i
                    );
                }
            }
            Err(e) => {
                if *expected_allowed {
                    panic!("Test case {}: expected success but got error: {:?}", i, e);
                }
                // Error is acceptable for rejected events
            }
        }
    }
}
