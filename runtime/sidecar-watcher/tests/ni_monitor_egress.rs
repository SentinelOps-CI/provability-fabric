/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 */

use sidecar_watcher::egress_cert::{EgressCertificate, WitnessVerification};
use sidecar_watcher::ni_monitor::{
    NIEvent, NIMonitor, NIMonitorConfig, SecurityLabel,
};
use std::collections::HashMap;

fn sample_ni_event() -> NIEvent {
    NIEvent {
        event_id: "event_1".to_string(),
        timestamp: 1_735_000_000,
        session_id: "session_123".to_string(),
        user_id: "user_123".to_string(),
        operation: "read".to_string(),
        input_labels: vec![SecurityLabel::Internal],
        output_labels: vec![SecurityLabel::Public],
        data_paths: vec!["$.data".to_string()],
        metadata: HashMap::new(),
    }
}

#[test]
fn test_ni_monitor_accepts_valid_event() {
    let mut monitor = NIMonitor::new(NIMonitorConfig::default());
    let result = monitor.monitor_event(sample_ni_event());
    assert!(result.is_ok(), "expected NI monitor to accept valid event");
}

#[test]
fn test_egress_certificate_sign_and_verify() {
    let mut cert = EgressCertificate::new(
        "session-1".to_string(),
        "bundle-1".to_string(),
        "plan-hash".to_string(),
        "policy-hash".to_string(),
    );
    cert.content.witness_verification = WitnessVerification {
        merkle_path_valid: true,
        field_commit_valid: true,
        label_derivation_valid: true,
        witness_hash: "witness".to_string(),
        verification_time_ms: 1,
    };
    assert!(cert.sign("private-key").is_ok());
    assert!(cert.verify_signature().unwrap());
}

#[test]
fn test_egress_certificate_schema_fields() {
    let cert = EgressCertificate::new(
        "session-1".to_string(),
        "bundle-1".to_string(),
        "plan-hash".to_string(),
        "policy-hash".to_string(),
    );
    assert_eq!(cert.content.metadata.version, "v2.0");
    assert!(!cert.content.metadata.session_id.is_empty());
}
