/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fs;
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use zip::{ZipArchive, ZipWriter};

/// Safety case bundle metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafetyCaseMetadata {
    pub session_id: String,
    pub bundle_id: String,
    pub created_at: u64,
    pub expires_at: u64,
    pub version: String,
    pub components: Vec<String>,
    pub total_size_bytes: u64,
    pub checksum: String,
}

/// Capability receipt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapabilityReceipt {
    pub capability_id: String,
    pub granted_at: u64,
    pub expires_at: u64,
    pub granted_by: String,
    pub scope: String,
    pub conditions: HashMap<String, String>,
    pub signature: String,
}

/// Plan execution record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlanExecutionRecord {
    pub plan_id: String,
    pub execution_id: String,
    pub start_time: u64,
    pub end_time: u64,
    pub status: String,
    pub capabilities_used: Vec<String>,
    pub events_processed: u64,
    pub plan_hash: String,
}

/// Kernel decision log entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KernelDecisionLog {
    pub timestamp: u64,
    pub decision_type: String,
    pub resource: String,
    pub action: String,
    pub result: String,
    pub justification: String,
    pub metadata: HashMap<String, String>,
}

/// Egress certificate
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressCertificate {
    pub certificate_id: String,
    pub issued_at: u64,
    pub expires_at: u64,
    pub subject: String,
    pub issuer: String,
    pub public_key: String,
    pub signature: String,
    pub extensions: HashMap<String, String>,
}

/// Attestation quote
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AttestationQuote {
    pub quote_id: String,
    pub timestamp: u64,
    pub platform: String,
    pub measurement: String,
    pub signature: String,
    pub public_key: String,
    pub nonce: String,
}

/// Safety case bundle
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafetyCaseBundle {
    pub metadata: SafetyCaseMetadata,
    pub capability_receipts: Vec<CapabilityReceipt>,
    pub plan_executions: Vec<PlanExecutionRecord>,
    pub kernel_decisions: Vec<KernelDecisionLog>,
    pub egress_certificates: Vec<EgressCertificate>,
    pub attestation_quotes: Vec<AttestationQuote>,
    pub artifacts: HashMap<String, Vec<u8>>,
}

/// Safety case builder
pub struct SafetyCaseBuilder {
    session_id: String,
    bundle_id: String,
    output_dir: PathBuf,
    retention_days: u32,
}

impl SafetyCaseBuilder {
    /// Create new safety case builder
    pub fn new(session_id: String, bundle_id: String, output_dir: PathBuf) -> Self {
        Self {
            session_id,
            bundle_id,
            output_dir,
            retention_days: 90, // Default 90-day retention
        }
    }

    /// Set retention policy
    pub fn with_retention(mut self, days: u32) -> Self {
        self.retention_days = days;
        self
    }

    /// Build safety case bundle
    pub fn build(&self, components: SafetyCaseComponents) -> Result<SafetyCaseBundle, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let expires_at = now + (self.retention_days as u64 * 24 * 60 * 60);

        let metadata = SafetyCaseMetadata {
            session_id: self.session_id.clone(),
            bundle_id: self.bundle_id.clone(),
            created_at: now,
            expires_at,
            version: "1.0.0".to_string(),
            components: vec![
                "capability_receipts".to_string(),
                "plan_executions".to_string(),
                "kernel_decisions".to_string(),
                "egress_certificates".to_string(),
                "attestation_quotes".to_string(),
            ],
            total_size_bytes: 0,      // Will be calculated
            checksum: "".to_string(), // Will be calculated
        };

        let mut bundle = SafetyCaseBundle {
            metadata,
            capability_receipts: components.capability_receipts,
            plan_executions: components.plan_executions,
            kernel_decisions: components.kernel_decisions,
            egress_certificates: components.egress_certificates,
            attestation_quotes: components.attestation_quotes,
            artifacts: HashMap::new(),
        };

        // Calculate total size and checksum
        let bundle_bytes = serde_json::to_vec(&bundle)
            .map_err(|e| format!("Failed to serialize bundle: {}", e))?;

        bundle.metadata.total_size_bytes = bundle_bytes.len() as u64;
        bundle.metadata.checksum = self.calculate_checksum(&bundle_bytes);

        Ok(bundle)
    }

    /// Save safety case bundle to file
    pub fn save_bundle(&self, bundle: &SafetyCaseBundle) -> Result<PathBuf, String> {
        let filename = format!(
            "safety_case_{}_{}_{}.json",
            self.session_id, self.bundle_id, bundle.metadata.created_at
        );

        let filepath = self.output_dir.join(&filename);

        let bundle_json = serde_json::to_string_pretty(bundle)
            .map_err(|e| format!("Failed to serialize bundle: {}", e))?;

        fs::write(&filepath, bundle_json)
            .map_err(|e| format!("Failed to write bundle file: {}", e))?;

        Ok(filepath)
    }

    /// Create ZIP archive of safety case bundle
    pub fn create_zip_archive(&self, bundle: &SafetyCaseBundle) -> Result<PathBuf, String> {
        let filename = format!(
            "safety_case_{}_{}_{}.zip",
            self.session_id, self.bundle_id, bundle.metadata.created_at
        );

        let filepath = self.output_dir.join(&filename);

        let file =
            fs::File::create(&filepath).map_err(|e| format!("Failed to create ZIP file: {}", e))?;

        let mut zip = ZipWriter::new(file);

        // Add bundle JSON
        let bundle_json = serde_json::to_string_pretty(bundle)
            .map_err(|e| format!("Failed to serialize bundle: {}", e))?;

        zip.start_file("bundle.json", zip::write::FileOptions::default())
            .map_err(|e| format!("Failed to add bundle.json to ZIP: {}", e))?;
        zip.write_all(bundle_json.as_bytes())
            .map_err(|e| format!("Failed to write bundle.json to ZIP: {}", e))?;

        // Add capability receipts
        for (i, receipt) in bundle.capability_receipts.iter().enumerate() {
            let receipt_json = serde_json::to_string_pretty(receipt)
                .map_err(|e| format!("Failed to serialize receipt {}: {}", i, e))?;

            let filename = format!("capability_receipts/{}.json", receipt.capability_id);
            zip.start_file(&filename, zip::write::FileOptions::default())
                .map_err(|e| format!("Failed to add receipt to ZIP: {}", e))?;
            zip.write_all(receipt_json.as_bytes())
                .map_err(|e| format!("Failed to write receipt to ZIP: {}", e))?;
        }

        // Add plan executions
        for (i, execution) in bundle.plan_executions.iter().enumerate() {
            let execution_json = serde_json::to_string_pretty(execution)
                .map_err(|e| format!("Failed to serialize execution {}: {}", i, e))?;

            let filename = format!("plan_executions/{}.json", execution.execution_id);
            zip.start_file(&filename, zip::write::FileOptions::default())
                .map_err(|e| format!("Failed to add execution to ZIP: {}", e))?;
            zip.write_all(execution_json.as_bytes())
                .map_err(|e| format!("Failed to write execution to ZIP: {}", e))?;
        }

        // Add kernel decisions
        let decisions_json = serde_json::to_string_pretty(&bundle.kernel_decisions)
            .map_err(|e| format!("Failed to serialize kernel decisions: {}", e))?;

        zip.start_file("kernel_decisions.json", zip::write::FileOptions::default())
            .map_err(|e| format!("Failed to add kernel decisions to ZIP: {}", e))?;
        zip.write_all(decisions_json.as_bytes())
            .map_err(|e| format!("Failed to write kernel decisions to ZIP: {}", e))?;

        // Add egress certificates
        for (i, cert) in bundle.egress_certificates.iter().enumerate() {
            let cert_json = serde_json::to_string_pretty(cert)
                .map_err(|e| format!("Failed to serialize certificate {}: {}", i, e))?;

            let filename = format!("egress_certificates/{}.json", cert.certificate_id);
            zip.start_file(&filename, zip::write::FileOptions::default())
                .map_err(|e| format!("Failed to add certificate to ZIP: {}", e))?;
            zip.write_all(cert_json.as_bytes())
                .map_err(|e| format!("Failed to write certificate to ZIP: {}", e))?;
        }

        // Add attestation quotes
        for (i, quote) in bundle.attestation_quotes.iter().enumerate() {
            let quote_json = serde_json::to_string_pretty(quote)
                .map_err(|e| format!("Failed to serialize quote {}: {}", i, e))?;

            let filename = format!("attestation_quotes/{}.json", quote.quote_id);
            zip.start_file(&filename, zip::write::FileOptions::default())
                .map_err(|e| format!("Failed to add quote to ZIP: {}", e))?;
            zip.write_all(quote_json.as_bytes())
                .map_err(|e| format!("Failed to write quote to ZIP: {}", e))?;
        }

        // Add artifacts
        for (name, data) in &bundle.artifacts {
            let filename = format!("artifacts/{}", name);
            zip.start_file(&filename, zip::write::FileOptions::default())
                .map_err(|e| format!("Failed to add artifact {} to ZIP: {}", name, e))?;
            zip.write_all(data)
                .map_err(|e| format!("Failed to write artifact {} to ZIP: {}", name, e))?;
        }

        zip.finish()
            .map_err(|e| format!("Failed to finalize ZIP: {}", e))?;

        Ok(filepath)
    }

    /// Validate safety case bundle
    pub fn validate_bundle(&self, bundle: &SafetyCaseBundle) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        // Check required fields
        if bundle.metadata.session_id.is_empty() {
            errors.push("Session ID is empty".to_string());
        }

        if bundle.metadata.bundle_id.is_empty() {
            errors.push("Bundle ID is empty".to_string());
        }

        // Check expiration
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        if bundle.metadata.expires_at <= now {
            errors.push("Bundle has expired".to_string());
        }

        // Check checksum
        let bundle_bytes = serde_json::to_vec(bundle).unwrap();
        let expected_checksum = self.calculate_checksum(&bundle_bytes);
        if bundle.metadata.checksum != expected_checksum {
            errors.push("Bundle checksum mismatch".to_string());
        }

        // Check capability receipts
        for (i, receipt) in bundle.capability_receipts.iter().enumerate() {
            if receipt.capability_id.is_empty() {
                errors.push(format!("Capability receipt {} has empty ID", i));
            }
            if receipt.expires_at <= now {
                errors.push(format!("Capability receipt {} has expired", i));
            }
        }

        // Check plan executions
        for (i, execution) in bundle.plan_executions.iter().enumerate() {
            if execution.plan_id.is_empty() {
                errors.push(format!("Plan execution {} has empty plan ID", i));
            }
            if execution.execution_id.is_empty() {
                errors.push(format!("Plan execution {} has empty execution ID", i));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Calculate checksum for data
    fn calculate_checksum(&self, data: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(data);
        format!("{:x}", hasher.finalize())
    }

    /// Clean up expired bundles
    pub fn cleanup_expired(&self) -> Result<u32, String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut cleaned_count = 0;

        for entry in fs::read_dir(&self.output_dir)
            .map_err(|e| format!("Failed to read output directory: {}", e))?
        {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;

            let path = entry.path();
            if path.is_file() {
                if let Some(extension) = path.extension() {
                    if extension == "json" || extension == "zip" {
                        // Try to extract timestamp from filename
                        if let Some(filename) = path.file_name() {
                            let filename_str = filename.to_string_lossy();
                            if let Some(timestamp_str) = filename_str.split('_').last() {
                                if let Some(timestamp_str) = timestamp_str.split('.').next() {
                                    if let Ok(timestamp) = timestamp_str.parse::<u64>() {
                                        if timestamp < now {
                                            fs::remove_file(&path).map_err(|e| {
                                                format!(
                                                    "Failed to remove expired file {}: {}",
                                                    path.display(),
                                                    e
                                                )
                                            })?;
                                            cleaned_count += 1;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        Ok(cleaned_count)
    }
}

/// Components for building safety case bundle
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SafetyCaseComponents {
    pub capability_receipts: Vec<CapabilityReceipt>,
    pub plan_executions: Vec<PlanExecutionRecord>,
    pub kernel_decisions: Vec<KernelDecisionLog>,
    pub egress_certificates: Vec<EgressCertificate>,
    pub attestation_quotes: Vec<AttestationQuote>,
}

impl Default for SafetyCaseComponents {
    fn default() -> Self {
        Self {
            capability_receipts: Vec::new(),
            plan_executions: Vec::new(),
            kernel_decisions: Vec::new(),
            egress_certificates: Vec::new(),
            attestation_quotes: Vec::new(),
        }
    }
}

/// Safety case store for managing multiple bundles
pub struct SafetyCaseStore {
    base_dir: PathBuf,
    retention_days: u32,
}

impl SafetyCaseStore {
    /// Create new safety case store
    pub fn new(base_dir: PathBuf) -> Self {
        Self {
            base_dir,
            retention_days: 90,
        }
    }

    /// Set retention policy
    pub fn with_retention(mut self, days: u32) -> Self {
        self.retention_days = days;
        self
    }

    /// Store safety case bundle
    pub fn store_bundle(&self, bundle: &SafetyCaseBundle) -> Result<PathBuf, String> {
        let session_dir = self.base_dir.join(&bundle.metadata.session_id);
        fs::create_dir_all(&session_dir)
            .map_err(|e| format!("Failed to create session directory: {}", e))?;

        let builder = SafetyCaseBuilder::new(
            bundle.metadata.session_id.clone(),
            bundle.metadata.bundle_id.clone(),
            session_dir,
        );

        builder.save_bundle(bundle)
    }

    /// Retrieve safety case bundle
    pub fn retrieve_bundle(
        &self,
        session_id: &str,
        bundle_id: &str,
    ) -> Result<SafetyCaseBundle, String> {
        let bundle_file = self
            .base_dir
            .join(session_id)
            .join(format!("safety_case_{}_{}_*.json", session_id, bundle_id));

        // Find matching file
        let mut bundle_path = None;
        for entry in fs::read_dir(self.base_dir.join(session_id))
            .map_err(|e| format!("Failed to read session directory: {}", e))?
        {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;

            let path = entry.path();
            if path.is_file() {
                if let Some(filename) = path.file_name() {
                    let filename_str = filename.to_string_lossy();
                    if filename_str
                        .starts_with(&format!("safety_case_{}_{}_", session_id, bundle_id))
                    {
                        bundle_path = Some(path);
                        break;
                    }
                }
            }
        }

        let bundle_path =
            bundle_path.ok_or_else(|| format!("Bundle not found: {}:{}", session_id, bundle_id))?;

        let bundle_content = fs::read_to_string(&bundle_path)
            .map_err(|e| format!("Failed to read bundle file: {}", e))?;

        let bundle: SafetyCaseBundle = serde_json::from_str(&bundle_content)
            .map_err(|e| format!("Failed to parse bundle JSON: {}", e))?;

        Ok(bundle)
    }

    /// List all bundles for a session
    pub fn list_session_bundles(&self, session_id: &str) -> Result<Vec<String>, String> {
        let session_dir = self.base_dir.join(session_id);
        if !session_dir.exists() {
            return Ok(Vec::new());
        }

        let mut bundles = Vec::new();

        for entry in fs::read_dir(session_dir)
            .map_err(|e| format!("Failed to read session directory: {}", e))?
        {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;

            let path = entry.path();
            if path.is_file() {
                if let Some(filename) = path.file_name() {
                    let filename_str = filename.to_string_lossy();
                    if filename_str.starts_with(&format!("safety_case_{}_", session_id)) {
                        if let Some(bundle_id) = filename_str.split('_').nth(2) {
                            bundles.push(bundle_id.to_string());
                        }
                    }
                }
            }
        }

        Ok(bundles)
    }

    /// Clean up expired bundles across all sessions
    pub fn cleanup_all_expired(&self) -> Result<u32, String> {
        let mut total_cleaned = 0;

        for entry in fs::read_dir(&self.base_dir)
            .map_err(|e| format!("Failed to read base directory: {}", e))?
        {
            let entry = entry.map_err(|e| format!("Failed to read directory entry: {}", e))?;

            let path = entry.path();
            if path.is_dir() {
                let builder = SafetyCaseBuilder::new(
                    path.file_name().unwrap().to_string_lossy().to_string(),
                    "".to_string(),
                    path,
                );

                let cleaned = builder.cleanup_expired()?;
                total_cleaned += cleaned;
            }
        }

        Ok(total_cleaned)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_safety_case_builder() {
        let temp_dir = tempdir().unwrap();
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );

        let components = SafetyCaseComponents::default();
        let bundle = builder.build(components).unwrap();

        assert_eq!(bundle.metadata.session_id, "test_session");
        assert_eq!(bundle.metadata.bundle_id, "test_bundle");
        assert!(!bundle.metadata.checksum.is_empty());
    }

    #[test]
    fn test_bundle_validation() {
        let temp_dir = tempdir().unwrap();
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );

        let components = SafetyCaseComponents::default();
        let bundle = builder.build(components).unwrap();

        let validation = builder.validate_bundle(&bundle);
        assert!(validation.is_ok());
    }

    #[test]
    fn test_bundle_storage() {
        let temp_dir = tempdir().unwrap();
        let store = SafetyCaseStore::new(temp_dir.path().to_path_buf());

        let components = SafetyCaseComponents::default();
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );

        let bundle = builder.build(components).unwrap();
        let stored_path = store.store_bundle(&bundle).unwrap();

        assert!(stored_path.exists());

        let retrieved_bundle = store
            .retrieve_bundle("test_session", "test_bundle")
            .unwrap();
        assert_eq!(retrieved_bundle.metadata.session_id, "test_session");
    }

    #[test]
    fn test_zip_archive_creation() {
        let temp_dir = tempdir().unwrap();
        let builder = SafetyCaseBuilder::new(
            "test_session".to_string(),
            "test_bundle".to_string(),
            temp_dir.path().to_path_buf(),
        );

        let components = SafetyCaseComponents::default();
        let bundle = builder.build(components).unwrap();

        let zip_path = builder.create_zip_archive(&bundle).unwrap();
        assert!(zip_path.exists());
        assert_eq!(zip_path.extension().unwrap(), "zip");
    }
}
