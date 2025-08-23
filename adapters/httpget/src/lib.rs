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
        }
    }
}

/// HTTP response with security metadata
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

/// HTTP-GET adapter with security enforcement
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
        
        Ok(())
    }
    
    /// Execute HTTP-GET request with security enforcement
    pub async fn execute(&mut self, url: &str) -> Result<HttpGetResponse, Box<dyn Error>> {
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
        })
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
        };
        
        assert!(HttpGetAdapter::validate_effect_signature(&restricted_effect).is_err());
    }
}
