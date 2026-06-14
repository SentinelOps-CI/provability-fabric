// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, Result};
use once_cell::sync::Lazy;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::fs::{create_dir_all, OpenOptions};
use std::io::Write;
use std::path::Path;

static CERT_SCHEMA: Lazy<Option<Value>> = Lazy::new(|| {
    let schema_path = std::env::var("CERT_V1_SCHEMA")
        .unwrap_or_else(|_| "external/CERT-V1/schema/cert-v1.schema.json".to_string());
    match std::fs::read_to_string(&schema_path) {
        Ok(data) => serde_json::from_str(&data).ok(),
        Err(_) => None,
    }
});

fn cert_schema() -> Result<&'static Value> {
    CERT_SCHEMA.as_ref().ok_or_else(|| {
        anyhow!(
            "CERT-V1 schema not available (clone with make submodules or set CERT_V1_SCHEMA)"
        )
    })
}

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
    let compiled = jsonschema::JSONSchema::compile(cert_schema()?)?;
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

/// Write CERT and optional Evidence v0.1 binding (additive JSONL event).
pub fn write_cert_with_binding(cert: &CertV1, session: &str, seq: u64, bundle_ref: Option<&str>) -> Result<String> {
    let path = write_cert(cert, session, seq)?;
    let mut binding = crate::evidence_v01::EvidenceV01Binding::new(session, &path);
    if let Some(ref_id) = bundle_ref {
        binding = binding.with_bundle_ref(ref_id);
    }
    if let Ok(digest) = digest_cert_file(&path) {
        binding = binding.with_artifact_digest("cert-v1", digest);
    }
    crate::evidence_v01::write_evidence_binding(&binding)?;
    Ok(path)
}

fn digest_cert_file(path: &str) -> Result<String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;
    let mut file = std::fs::File::open(path)?;
    let mut buf = Vec::new();
    file.read_to_end(&mut buf)?;
    let sum = Sha256::digest(&buf);
    Ok(format!("sha256:{:x}", sum))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::{BufRead, BufReader};
    use std::path::{Path, PathBuf};

    fn cert_schema_available() -> bool {
        Path::new("external/CERT-V1/schema/cert-v1.schema.json").exists()
    }

    fn sample_cert() -> CertV1 {
        CertV1 {
            bundle_id: "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string(),
            policy_hash: "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string(),
            proof_hash: "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string(),
            automata_hash: "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd".to_string(),
            labeler_hash: "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee".to_string(),
            ni_monitor: "accept".to_string(),
            permit_decision: "accept".to_string(),
            path_witness_ok: true,
            label_derivation_ok: true,
            epoch: 1,
            sidecar_build: "test@1.0".to_string(),
            egress_profile: "EGRESS-DET-P1@1.0".to_string(),
            morph: None,
            sig: "unconfigured".to_string(),
        }
    }

    #[test]
    fn write_cert_with_binding_emits_binding_jsonl() {
        if !cert_schema_available() {
            eprintln!("skip: CERT-V1 schema missing");
            return;
        }

        let tmp = tempfile::TempDir::new().expect("tempdir");
        std::env::set_current_dir(tmp.path()).expect("chdir");

        let cert = sample_cert();
        let bundle_ref = "examples/runtime-evidence-basic/basic-evidence-bundle.json";
        let path = write_cert_with_binding(&cert, "runtime-demo-001", 1, Some(bundle_ref))
            .expect("write cert with binding");
        assert!(Path::new(&path).is_file(), "cert file written");

        let log_path = PathBuf::from("evidence/logs/sidecar.jsonl");
        assert!(log_path.is_file(), "expected sidecar.jsonl");

        let file = fs::File::open(&log_path).expect("open log");
        let lines: Vec<String> = BufReader::new(file)
            .lines()
            .map(|l| l.expect("read line"))
            .collect();
        assert!(lines.len() >= 2, "expected cert line and binding line");

        let binding_line = lines.last().expect("binding line");
        let parsed: crate::evidence_v01::EvidenceV01Binding =
            serde_json::from_str(binding_line).expect("binding JSONL");
        assert_eq!(parsed.event_type, "evidence_v01_binding");
        assert_eq!(parsed.evidence_bundle_ref.as_deref(), Some(bundle_ref));
        assert!(parsed.artifact_digests.contains_key("cert-v1"));
    }
}
