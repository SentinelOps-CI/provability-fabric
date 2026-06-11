// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::{create_dir_all, OpenOptions};
use std::io::Write;
use std::path::Path;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EvidenceV01Binding {
    pub event_type: String,
    pub session_id: String,
    pub cert_path: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence_bundle_ref: Option<String>,
    pub artifact_digests: BTreeMap<String, String>,
    pub schema_version: String,
}

impl EvidenceV01Binding {
    pub fn new(session_id: &str, cert_path: &str) -> Self {
        Self {
            event_type: "evidence_v01_binding".to_string(),
            session_id: session_id.to_string(),
            cert_path: cert_path.to_string(),
            evidence_bundle_ref: None,
            artifact_digests: BTreeMap::new(),
            schema_version: "0.1".to_string(),
        }
    }

    pub fn with_bundle_ref(mut self, bundle_ref: &str) -> Self {
        self.evidence_bundle_ref = Some(bundle_ref.to_string());
        self
    }

    pub fn with_artifact_digest(mut self, role: &str, digest: String) -> Self {
        self.artifact_digests.insert(role.to_string(), digest);
        self
    }
}

pub fn write_evidence_binding(binding: &EvidenceV01Binding) -> Result<()> {
    let log_dir = Path::new("evidence/logs");
    if !log_dir.exists() {
        create_dir_all(log_dir)?;
    }
    let log_path = log_dir.join("sidecar.jsonl");
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(log_path)?;
    let line = serde_json::to_string(binding)?;
    writeln!(file, "{}", line)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn binding_serializes_event_type() {
        let b = EvidenceV01Binding::new("sess", "evidence/certs/sess/1.cert.json");
        assert_eq!(b.event_type, "evidence_v01_binding");
        assert_eq!(b.schema_version, "0.1");
    }
}
