// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use serde_json::Value;
use sidecar_watcher::runtime_observation::emit_from_audit_json;
use std::fs;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn catalog_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/capability_catalog.json")
}

fn schema_path() -> Option<PathBuf> {
    let candidates = [
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../../vendor/pf-core/schemas/runtime_observation.v1.schema.json"),
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("schemas/runtime_observation.v1.schema.json"),
    ];
    candidates.into_iter().find(|p| p.is_file())
}

fn validate_against_schema(obs: &Value) {
    let Some(schema_path) = schema_path() else {
        eprintln!("SKIP schema validation: runtime_observation.v1.schema.json not present");
        return;
    };
    let schema_text = fs::read_to_string(&schema_path).expect("read schema");
    let schema: Value = serde_json::from_str(&schema_text).expect("parse schema");
    let compiled = jsonschema::JSONSchema::compile(&schema).expect("compile schema");
    match compiled.validate(obs) {
        Ok(()) => {}
        Err(errors) => {
            let msgs: Vec<String> = errors.map(|e| e.to_string()).collect();
            panic!("schema validation failed: {}", msgs.join("; "));
        }
    };
}

#[test]
fn emit_golden_allowed_observation() {
    let text = fs::read_to_string(fixture("sidecar_audit_line.json")).unwrap();
    let obs = emit_from_audit_json(&text, &catalog_path()).unwrap();
    assert_eq!(obs["decision"], "allowed");
    assert_eq!(obs["principal"]["roles"][0], "mcp_user");
    validate_against_schema(&obs);
}

#[test]
fn emit_golden_denied_observation() {
    let text = fs::read_to_string(fixture("sidecar_denied_audit_line.json")).unwrap();
    let obs = emit_from_audit_json(&text, &catalog_path()).unwrap();
    assert_eq!(obs["decision"], "denied");
    validate_against_schema(&obs);
}

#[test]
fn ambiguous_line_requires_capability_hint() {
    let text = fs::read_to_string(fixture("sidecar_ambiguous_audit_line.json")).unwrap();
    let err = emit_from_audit_json(&text, &catalog_path()).unwrap_err();
    assert!(err.to_string().contains("capability_hint"));
}
