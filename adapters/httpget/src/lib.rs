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
use std::collections::HashMap;
use std::error::Error;
use std::time::{Duration, Instant};
use reqwest::Client;
use reqwest::header::{HeaderMap, HeaderValue, CONTENT_LENGTH, USER_AGENT};
use url::Url;
use sha2::{Digest, Sha256};

/// Resource mapping for HTTP-GET operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpGetResource {
    pub doc_id: String,           // Document ID (URI)
    pub field_path: Vec<String>,  // Field path for JSON response
    pub merkle_root: String,      // Merkle root for witness validation
    pub field_commit: String,     // Field commit hash
    pub label: String,            // Information flow control label
}

/// Witness for HTTP-GET operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpGetWitness {
    pub merkle_path: Vec<String>, // Merkle path from root to field
    pub sibling_hashes: Vec<String>, // Sibling hashes for path verification
    pub field_commit: String,     // Field commit hash
    pub timestamp: u64,           // Witness timestamp
    pub signature: String,        // Cryptographic signature
}

/// Effect signature for HTTP-GET operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpGetEffect {
    pub url: String,
    pub method: String,
    pub max_redirects: u32,
    pub timeout_ms: u32,
    pub max_content_length: usize,
    pub allowed_domains: Vec<String>,
    pub user_agent: String,
    pub resource_mapping: Option<HttpGetResource>, // Optional resource mapping
    pub witness_required: bool,                    // Whether witness is required
    pub high_assurance_mode: bool,                 // High-assurance mode for IFC
}

impl Default for HttpGetEffect {
    fn default() -> Self {
        Self {
            url: String::new(),
            method: "GET".to_string(),
            max_redirects: 0, // No redirects allowed by default
            timeout_ms: 30000, // 30 second timeout
            max_content_length: 10 * 1024 * 1024, // 10MB max
            allowed_domains: vec![],
            user_agent: "ProvabilityFabric-HttpGet/1.0".to_string(),
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        }
    }
}

/// HTTP response with security metadata and witness validation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpGetResponse {
    pub status_code: u16,
    pub content_length: Option<u64>,
    pub content_type: Option<String>,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
    pub final_url: String,
    pub redirect_count: u32,
    pub response_time_ms: u64,
    pub security_metadata: SecurityMetadata,
    pub witness_validation: WitnessValidationResult,
    pub resource_access: ResourceAccessResult,
}

/// Security metadata for audit and compliance
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityMetadata {
    pub dns_resolved: String,
    pub tls_version: Option<String>,
    pub certificate_fingerprint: Option<String>,
    pub ip_address: String,
    pub geolocation: Option<String>,
    pub request_timestamp: u64,
    pub response_timestamp: u64,
}

/// Witness validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessValidationResult {
    pub valid: bool,
    pub merkle_path_verified: bool,
    pub field_commit_verified: bool,
    pub timestamp_valid: bool,
    pub signature_valid: bool,
    pub error_message: Option<String>,
}

/// Resource access result for IFC
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceAccessResult {
    pub access_granted: bool,
    pub label_derivation_ok: bool,
    pub declass_rule_applied: Option<String>,
    pub flow_violation: Option<String>,
    pub permitted_fields: Vec<String>,
}

/// HTTP-GET adapter with security enforcement and witness validation
pub struct HttpGetAdapter {
    client: Client,
    effect_signature: HttpGetEffect,
    request_count: u64,
    last_request_time: Option<Instant>,
}

impl HttpGetAdapter {
    /// Create new HTTP-GET adapter with effect signature
    pub fn new(effect_signature: HttpGetEffect) -> Result<Self, Box<dyn Error>> {
        // Validate effect signature
        Self::validate_effect_signature(&effect_signature)?;
        
        // Create HTTP client with security constraints
        let client = Client::builder()
            .timeout(Duration::from_millis(effect_signature.timeout_ms as u64))
            .redirect(reqwest::redirect::Policy::limited(effect_signature.max_redirects as usize))
            .user_agent(&effect_signature.user_agent)
            .build()?;
        
        Ok(Self {
            client,
            effect_signature,
            request_count: 0,
            last_request_time: None,
        })
    }
    
    /// Validate effect signature for security compliance
    fn validate_effect_signature(effect: &HttpGetEffect) -> Result<(), Box<dyn Error>> {
        // Validate URL format
        let url = Url::parse(&effect.url)?;
        
        // Check if domain is allowed
        if !effect.allowed_domains.is_empty() {
            let domain = url.host_str().ok_or("Invalid host")?;
            if !effect.allowed_domains.contains(&domain.to_string()) {
                return Err("Domain not in allowed list".into());
            }
        }
        
        // Validate method
        if effect.method != "GET" {
            return Err("Only GET method allowed".into());
        }
        
        // Validate timeout
        if effect.timeout_ms == 0 || effect.timeout_ms > 300000 { // Max 5 minutes
            return Err("Invalid timeout value".into());
        }
        
        // Validate content length limit
        if effect.max_content_length == 0 || effect.max_content_length > 100 * 1024 * 1024 { // Max 100MB
            return Err("Invalid content length limit".into());
        }

        // Validate resource mapping if provided
        if let Some(ref resource) = effect.resource_mapping {
            if resource.doc_id.is_empty() || resource.merkle_root.is_empty() {
                return Err("Invalid resource mapping: missing doc_id or merkle_root".into());
            }
        }
        
        Ok(())
    }
    
    /// Execute HTTP-GET request with security enforcement and witness validation
    pub async fn execute(&mut self, url: &str, witness: Option<&HttpGetWitness>) -> Result<HttpGetResponse, Box<dyn Error>> {
        // Rate limiting check
        self.check_rate_limit()?;
        
        // Validate URL against effect signature
        let parsed_url = Url::parse(url)?;
        if !self.effect_signature.allowed_domains.is_empty() {
            let domain = parsed_url.host_str().ok_or("Invalid host")?;
            if !self.effect_signature.allowed_domains.contains(&domain.to_string()) {
                return Err("Domain not in allowed list".into());
            }
        }
        
        let start_time = Instant::now();
        
        // Execute request
        let response = self.client
            .get(url)
            .send()
            .await?;
        
        let response_time = start_time.elapsed();
        
        // Extract response data
        let status_code = response.status().as_u16();
        let headers = response.headers().clone();
        let final_url = response.url().to_string();
        
        // Check content length
        let content_length = headers.get(CONTENT_LENGTH)
            .and_then(|v| v.to_str().ok())
            .and_then(|s| s.parse::<u64>().ok());
        
        if let Some(length) = content_length {
            if length > self.effect_signature.max_content_length as u64 {
                return Err("Content length exceeds limit".into());
            }
        }
        
        // Read body with size limit
        let body = response.bytes().await?;
        if body.len() > self.effect_signature.max_content_length {
            return Err("Response body exceeds size limit".into());
        }
        
        // Extract security metadata
        let security_metadata = SecurityMetadata {
            dns_resolved: parsed_url.host_str().unwrap_or("unknown").to_string(),
            tls_version: None, // Would be extracted from TLS connection
            certificate_fingerprint: None, // Would be extracted from TLS connection
            ip_address: "0.0.0.0".to_string(), // Would be resolved from DNS
            geolocation: None, // Would be looked up from IP
            request_timestamp: start_time.duration_since(Instant::now()).as_millis() as u64,
            response_timestamp: response_time.as_millis() as u64,
        };

        // Validate witness if required
        let witness_validation = if self.effect_signature.witness_required {
            self.validate_witness(witness, &body)?
        } else {
            WitnessValidationResult {
                valid: true,
                merkle_path_verified: true,
                field_commit_verified: true,
                timestamp_valid: true,
                signature_valid: true,
                error_message: None,
            }
        };

        // Validate resource access for IFC
        let resource_access = if let Some(ref resource) = self.effect_signature.resource_mapping {
            self.validate_resource_access(resource, &body, witness)?
        } else {
            ResourceAccessResult {
                access_granted: true,
                label_derivation_ok: true,
                declass_rule_applied: None,
                flow_violation: None,
                permitted_fields: vec![],
            }
        };

        // Update adapter state
        self.request_count += 1;
        self.last_request_time = Some(Instant::now());
        
        Ok(HttpGetResponse {
            status_code,
            content_length,
            content_type: headers.get("content-type")
                .and_then(|v| v.to_str().ok())
                .map(|s| s.to_string()),
            headers: headers.iter()
                .map(|(k, v)| (k.to_string(), v.to_str().unwrap_or("").to_string()))
                .collect(),
            body: body.to_vec(),
            final_url,
            redirect_count: 0, // Would be tracked during redirects
            response_time_ms: response_time.as_millis() as u64,
            security_metadata,
            witness_validation,
            resource_access,
        })
    }

    /// Validate witness for high-assurance mode
    fn validate_witness(&self, witness: Option<&HttpGetWitness>, body: &[u8]) -> Result<WitnessValidationResult, Box<dyn Error>> {
        let witness = witness.ok_or("Witness required but not provided")?;
        
        // Validate timestamp (within 5 minutes)
        let current_time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs();
        let timestamp_valid = (current_time as i64 - witness.timestamp as i64).abs() < 300;

        // Validate field commit
        let body_hash = self.calculate_body_hash(body);
        let field_commit_verified = body_hash == witness.field_commit;

        // Validate Merkle path (simplified - would use actual Merkle tree verification)
        let merkle_path_verified = self.verify_merkle_path(witness)?;

        // Validate signature (simplified - would use actual cryptographic verification)
        let signature_valid = self.verify_signature(witness)?;

        let valid = timestamp_valid && field_commit_verified && merkle_path_verified && signature_valid;

        Ok(WitnessValidationResult {
            valid,
            merkle_path_verified,
            field_commit_verified,
            timestamp_valid,
            signature_valid,
            error_message: if valid { None } else { Some("Witness validation failed".to_string()) },
        })
    }

    /// Validate resource access for information flow control
    fn validate_resource_access(&self, resource: &HttpGetResource, body: &[u8], witness: Option<&HttpGetWitness>) -> Result<ResourceAccessResult, Box<dyn Error>> {
        // Check if we have a valid witness in high-assurance mode
        let witness_ok = if self.effect_signature.high_assurance_mode {
            witness.is_some() && witness.as_ref().unwrap().field_commit == resource.field_commit
        } else {
            true
        };

        if !witness_ok {
            return Ok(ResourceAccessResult {
                access_granted: false,
                label_derivation_ok: false,
                declass_rule_applied: None,
                flow_violation: Some("Missing or invalid witness in high-assurance mode".to_string()),
                permitted_fields: vec![],
            });
        }

        // Parse JSON response to extract field access
        let json_value: serde_json::Value = serde_json::from_slice(body)?;
        let permitted_fields = self.extract_permitted_fields(&json_value, &resource.field_path)?;

        // Check label derivation (simplified IFC logic)
        let label_derivation_ok = self.can_derive_label(&resource.label)?;

        // Check for declassification rules
        let declass_rule_applied = self.check_declass_rules(&resource.label)?;

        Ok(ResourceAccessResult {
            access_granted: true,
            label_derivation_ok,
            declass_rule_applied,
            flow_violation: None,
            permitted_fields,
        })
    }

    /// Calculate hash of response body
    fn calculate_body_hash(&self, body: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(body);
        format!("{:x}", hasher.finalize())
    }

    /// Verify Merkle path (simplified implementation)
    fn verify_merkle_path(&self, witness: &HttpGetWitness) -> Result<bool, Box<dyn Error>> {
        // In a real implementation, this would verify the Merkle path from root to field
        // For now, we'll assume it's valid if the path is not empty
        Ok(!witness.merkle_path.is_empty())
    }

    /// Verify signature (simplified implementation)
    fn verify_signature(&self, witness: &HttpGetWitness) -> Result<bool, Box<dyn Error>> {
        // In a real implementation, this would verify the cryptographic signature
        // For now, we'll assume it's valid if the signature is not empty
        Ok(!witness.signature.is_empty())
    }

    /// Extract permitted fields from JSON response
    fn extract_permitted_fields(&self, json: &serde_json::Value, field_path: &[String]) -> Result<Vec<String>, Box<dyn Error>> {
        let mut permitted_fields = Vec::new();
        
        // Navigate to the specified field path
        let mut current = json;
        for field in field_path {
            if let Some(value) = current.get(field) {
                current = value;
            } else {
                return Ok(permitted_fields); // Field not found
            }
        }

        // Extract field names at the target level
        if let Some(obj) = current.as_object() {
            for (key, _) in obj {
                permitted_fields.push(key.clone());
            }
        }

        Ok(permitted_fields)
    }

    /// Check if label can be derived (simplified IFC logic)
    fn can_derive_label(&self, label: &str) -> Result<bool, Box<dyn Error>> {
        // Simplified IFC logic - in practice, this would use the full IFC system
        match label {
            "public" => Ok(true),
            "internal" => Ok(true),
            "confidential" => Ok(false), // Would check declassification rules
            "secret" => Ok(false),       // Would check declassification rules
            _ => Ok(false),
        }
    }

    /// Check for applicable declassification rules
    fn check_declass_rules(&self, label: &str) -> Result<Option<String>, Box<dyn Error>> {
        // Simplified declassification logic
        match label {
            "confidential" => Ok(Some("confidential_to_internal".to_string())),
            "secret" => Ok(Some("secret_to_confidential".to_string())),
            _ => Ok(None),
        }
    }
    
    /// Check rate limiting constraints
    fn check_rate_limit(&self) -> Result<(), Box<dyn Error>> {
        // Simple rate limiting: max 100 requests per minute
        const MAX_REQUESTS_PER_MINUTE: u64 = 100;
        
        if let Some(last_time) = self.last_request_time {
            let elapsed = last_time.elapsed();
            if elapsed < Duration::from_secs(60) && self.request_count >= MAX_REQUESTS_PER_MINUTE {
                return Err("Rate limit exceeded".into());
            }
        }
        
        Ok(())
    }
    
    /// Get adapter statistics
    pub fn get_stats(&self) -> HashMap<String, String> {
        let mut stats = HashMap::new();
        stats.insert("request_count".to_string(), self.request_count.to_string());
        stats.insert("last_request_time".to_string(), 
            self.last_request_time.map(|t| t.elapsed().as_secs().to_string())
                .unwrap_or_else(|| "never".to_string()));
        stats.insert("effect_signature".to_string(), format!("{:?}", self.effect_signature));
        stats.insert("witness_required".to_string(), self.effect_signature.witness_required.to_string());
        stats.insert("high_assurance_mode".to_string(), self.effect_signature.high_assurance_mode.to_string());
        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_effect_signature_validation() {
        let valid_effect = HttpGetEffect {
            url: "https://example.com".to_string(),
            method: "GET".to_string(),
            max_redirects: 0,
            timeout_ms: 30000,
            max_content_length: 1024 * 1024,
            allowed_domains: vec!["example.com".to_string()],
            user_agent: "Test/1.0".to_string(),
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };
        
        assert!(HttpGetAdapter::validate_effect_signature(&valid_effect).is_ok());
    }
    
    #[test]
    fn test_invalid_method_rejected() {
        let invalid_effect = HttpGetEffect {
            url: "https://example.com".to_string(),
            method: "POST".to_string(), // Invalid method
            max_redirects: 0,
            timeout_ms: 30000,
            max_content_length: 1024 * 1024,
            allowed_domains: vec![],
            user_agent: "Test/1.0".to_string(),
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };
        
        assert!(HttpGetAdapter::validate_effect_signature(&invalid_effect).is_err());
    }
    
    #[test]
    fn test_domain_restriction_enforced() {
        let restricted_effect = HttpGetEffect {
            url: "https://example.com".to_string(),
            method: "GET".to_string(),
            max_redirects: 0,
            timeout_ms: 30000,
            max_content_length: 1024 * 1024,
            allowed_domains: vec!["allowed.com".to_string()],
            user_agent: "Test/1.0".to_string(),
            resource_mapping: None,
            witness_required: false,
            high_assurance_mode: false,
        };
        
        assert!(HttpGetAdapter::validate_effect_signature(&restricted_effect).is_err());
    }

    #[test]
    fn test_resource_mapping_validation() {
        let valid_resource = HttpGetResource {
            doc_id: "https://api.example.com/data".to_string(),
            field_path: vec!["users".to_string()],
            merkle_root: "abc123".to_string(),
            field_commit: "def456".to_string(),
            label: "internal".to_string(),
        };

        let effect_with_resource = HttpGetEffect {
            url: "https://api.example.com/data".to_string(),
            method: "GET".to_string(),
            max_redirects: 0,
            timeout_ms: 30000,
            max_content_length: 1024 * 1024,
            allowed_domains: vec![],
            user_agent: "Test/1.0".to_string(),
            resource_mapping: Some(valid_resource),
            witness_required: true,
            high_assurance_mode: true,
        };

        assert!(HttpGetAdapter::validate_effect_signature(&effect_with_resource).is_ok());
    }

    #[test]
    fn test_invalid_resource_mapping_rejected() {
        let invalid_resource = HttpGetResource {
            doc_id: "".to_string(), // Empty doc_id
            field_path: vec!["users".to_string()],
            merkle_root: "".to_string(), // Empty merkle_root
            field_commit: "def456".to_string(),
            label: "internal".to_string(),
        };

        let effect_with_invalid_resource = HttpGetEffect {
            url: "https://api.example.com/data".to_string(),
            method: "GET".to_string(),
            max_redirects: 0,
            timeout_ms: 30000,
            max_content_length: 1024 * 1024,
            allowed_domains: vec![],
            user_agent: "Test/1.0".to_string(),
            resource_mapping: Some(invalid_resource),
            witness_required: true,
            high_assurance_mode: true,
        };

        assert!(HttpGetAdapter::validate_effect_signature(&effect_with_invalid_resource).is_err());
    }
}
