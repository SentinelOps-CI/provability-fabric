// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use sidecar_watcher::permit_enforcement::{PermitEnforcementHook, RuntimeEvent};
use sidecar_watcher::policy_adapter::{EnforcementMode, PolicyConfig};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader};
use std::path::Path;

fn cert_schema_available() -> bool {
    Path::new("external/CERT-V1/schema/cert-v1.schema.json").exists()
}

#[test]
fn emit_evidence_binding_through_permit_enforcement() {
    if !cert_schema_available() {
        eprintln!("skip: CERT-V1 schema missing (make submodules)");
        return;
    }

    let tmp = tempfile::TempDir::new().expect("tempdir");
    std::env::set_current_dir(tmp.path()).expect("chdir");
    std::env::set_var(
        "BUNDLE_ID",
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    );
    std::env::set_var("POLICY_HASH", "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb");
    std::env::set_var("PROOF_HASH", "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc");
    std::env::set_var(
        "AUTOMATA_HASH",
        "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
    );
    std::env::set_var(
        "LABELER_HASH",
        "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
    );
    std::env::set_var(
        "EVIDENCE_BUNDLE_REF",
        "examples/runtime-evidence-basic/basic-evidence-bundle.json",
    );

    let config = PolicyConfig {
        enforcement_mode: EnforcementMode::Enforce,
        shadow_mode: false,
        epoch_validation: true,
        witness_validation: true,
        high_assurance_mode: false,
        feature_flags: HashMap::new(),
    };
    let mut hook = PermitEnforcementHook::new(config);

    let event = RuntimeEvent {
        event_id: "emit-001".to_string(),
        event_type: "emit".to_string(),
        user_id: "user1".to_string(),
        roles: vec!["admin".to_string()],
        organization: "org".to_string(),
        session_id: "emit-session-001".to_string(),
        epoch: 1,
        attributes: vec![],
        tenant: "tenantA".to_string(),
        timestamp: 42,
        resource_uri: None,
        resource_version: None,
        field_path: None,
        tool: None,
        args: None,
        merkle_witness: None,
        field_commit: None,
        source_label: None,
        target_label: None,
    };

    hook.process_event(&event).expect("process emit event");

    let cert_path = "evidence/certs/emit-session-001/42.cert.json";
    assert!(Path::new(cert_path).is_file(), "cert file written");

    let cert_bytes = fs::read(cert_path).expect("read cert");
    let expected_digest = format!("sha256:{:x}", Sha256::digest(&cert_bytes));

    let log_path = Path::new("evidence/logs/sidecar.jsonl");
    assert!(log_path.is_file(), "sidecar.jsonl exists");

    let lines: Vec<String> = BufReader::new(fs::File::open(log_path).expect("open log"))
        .lines()
        .map(|l| l.expect("line"))
        .collect();
    assert!(lines.len() >= 2, "expected cert + binding lines");

    let binding_line = lines.last().expect("binding");
    assert!(binding_line.contains("evidence_v01_binding"));
    assert!(binding_line.contains("examples/runtime-evidence-basic/basic-evidence-bundle.json"));
    assert!(binding_line.contains(&expected_digest));
}
