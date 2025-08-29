// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fs::{create_dir_all, OpenOptions};
use std::io::Write;
use std::path::Path;

static CERT_SCHEMA: Lazy<Value> = Lazy::new(|| {
    // Load the CERT-V1 schema from the submodule path at runtime
    let schema_path = std::env::var("CERT_V1_SCHEMA")
        .unwrap_or_else(|_| "external/CERT-V1/schema/cert-v1.schema.json".to_string());
    let data = std::fs::read_to_string(&schema_path)
        .unwrap_or_else(|e| panic!("Failed to read CERT-V1 schema {}: {}", schema_path, e));
    serde_json::from_str(&data).expect("Invalid CERT-V1 schema JSON")
});

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertV1 {
    pub bundle_id: String,
    pub policy_hash: String,
    pub proof_hash: String,
    pub automata_hash: String,
    pub labeler_hash: String,
    pub ni_monitor: String, // "inapplicable" | "accept" | "reject" | "error"
    pub permit_decision: String, // "accept" | "reject" | "error"
    pub path_witness_ok: bool,
    pub label_derivation_ok: bool,
    pub epoch: u64,
    pub sidecar_build: String,
    pub egress_profile: String, // e.g., EGRESS-DET-P1@1.0
    #[serde(skip_serializing_if = "Option::is_none")]
    pub morph: Option<MorphInfo>,
    pub sig: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MorphInfo {
    pub env_snapshot_digest: String,
    pub branch_id: String,
    pub base_image: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub morphvm_id: Option<String>,
}

pub fn validate_cert(cert: &CertV1) -> Result<()> {
    let compiled = jsonschema::JSONSchema::compile(&*CERT_SCHEMA)?;
    let data = serde_json::to_value(cert)?;
    let result = compiled.validate(&data);
    if let Err(errors) = result {
        let msgs: Vec<String> = errors.map(|e| e.to_string()).collect();
        return Err(anyhow!("CERT-V1 validation failed: {}", msgs.join("; ")));
    }
    Ok(())
}

pub fn write_cert(cert: &CertV1, session: &str, seq: u64) -> Result<String> {
    validate_cert(cert)?; // deny-wins if invalid

    let dir = format!("evidence/certs/{}", session);
    create_dir_all(&dir)?;
    let path = format!("{}/{}.cert.json", dir, seq);
    let json = serde_json::to_string_pretty(cert)?;
    std::fs::write(&path, json)?;

    // Append JSONL log
    let log_dir = Path::new("evidence/logs");
    if !log_dir.exists() {
        create_dir_all(log_dir)?;
    }
    let log_path = log_dir.join("sidecar.jsonl");
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(log_path)?;
    let line = serde_json::to_string(cert)?;
    writeln!(file, "{}", line)?;

    Ok(path)
}
