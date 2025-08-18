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

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Break glass configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BreakGlassConfig {
    pub enable_break_glass: bool,
    pub m_of_n_threshold: (usize, usize), // (M, N) where M <= N
    pub ttl_seconds: u64,
    pub auto_page_enabled: bool,
    pub auto_page_threshold: u64, // Time in seconds before auto-page
    pub require_justification: bool,
    pub audit_logging: bool,
    pub max_active_break_glass: usize,
}

impl Default for BreakGlassConfig {
    fn default() -> Self {
        Self {
            enable_break_glass: true,
            m_of_n_threshold: (2, 3), // 2 of 3 signatures required
            ttl_seconds: 3600, // 1 hour
            auto_page_enabled: true,
            auto_page_threshold: 300, // 5 minutes before auto-page
            require_justification: true,
            audit_logging: true,
            max_active_break_glass: 10,
        }
    }
}

/// Break glass request
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BreakGlassRequest {
    pub request_id: String,
    pub session_id: String,
    pub user_id: String,
    pub reason: String,
    pub justification: Option<String>,
    pub requested_operations: Vec<String>,
    pub requested_resources: Vec<String>,
    pub urgency_level: UrgencyLevel,
    pub created_at: u64,
    pub expires_at: u64,
    pub status: BreakGlassStatus,
    pub signatures: Vec<BreakGlassSignature>,
    pub metadata: HashMap<String, String>,
}

/// Urgency level for break glass requests
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum UrgencyLevel {
    Low,
    Medium,
    High,
    Critical,
    Emergency,
}

impl UrgencyLevel {
    /// Convert to string representation
    pub fn to_string(&self) -> &'static str {
        match self {
            UrgencyLevel::Low => "low",
            UrgencyLevel::Medium => "medium",
            UrgencyLevel::High => "high",
            UrgencyLevel::Critical => "critical",
            UrgencyLevel::Emergency => "emergency",
        }
    }

    /// Parse from string representation
    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "low" => Ok(UrgencyLevel::Low),
            "medium" => Ok(UrgencyLevel::Medium),
            "high" => Ok(UrgencyLevel::High),
            "critical" => Ok(UrgencyLevel::Critical),
            "emergency" => Ok(UrgencyLevel::Emergency),
            _ => Err(format!("Unknown urgency level: {}", s)),
        }
    }

    /// Get numeric value for comparison
    pub fn numeric_value(&self) -> u8 {
        match self {
            UrgencyLevel::Low => 1,
            UrgencyLevel::Medium => 2,
            UrgencyLevel::High => 3,
            UrgencyLevel::Critical => 4,
            UrgencyLevel::Emergency => 5,
        }
    }
}

/// Break glass status
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum BreakGlassStatus {
    Pending,
    Approved,
    Denied,
    Expired,
    AutoPaged,
    Completed,
}

impl BreakGlassStatus {
    /// Convert to string representation
    pub fn to_string(&self) -> &'static str {
        match self {
            BreakGlassStatus::Pending => "pending",
            BreakGlassStatus::Approved => "approved",
            BreakGlassStatus::Denied => "denied",
            BreakGlassStatus::Expired => "expired",
            BreakGlassStatus::AutoPaged => "auto_paged",
            BreakGlassStatus::Completed => "completed",
        }
    }
}

/// Break glass signature
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BreakGlassSignature {
    pub signer_id: String,
    pub signer_role: String,
    pub signature: String,
    pub timestamp: u64,
    pub justification: Option<String>,
    pub metadata: HashMap<String, String>,
}

/// Break glass manager
pub struct BreakGlassManager {
    config: BreakGlassConfig,
    active_requests: HashMap<String, BreakGlassRequest>,
    user_requests: HashMap<String, Vec<String>>,
    session_requests: HashMap<String, Vec<String>>,
    authorized_signers: HashSet<String>,
    last_cleanup: u64,
}

impl BreakGlassManager {
    /// Create new break glass manager
    pub fn new(config: BreakGlassConfig) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            config,
            active_requests: HashMap::new(),
            user_requests: HashMap::new(),
            session_requests: HashMap::new(),
            authorized_signers: HashSet::new(),
            last_cleanup: now,
        }
    }

    /// Add authorized signer
    pub fn add_authorized_signer(&mut self, signer_id: String) {
        self.authorized_signers.insert(signer_id);
    }

    /// Remove authorized signer
    pub fn remove_authorized_signer(&mut self, signer_id: &str) {
        self.authorized_signers.remove(signer_id);
    }

    /// Create break glass request
    pub fn create_request(
        &mut self,
        session_id: String,
        user_id: String,
        reason: String,
        justification: Option<String>,
        requested_operations: Vec<String>,
        requested_resources: Vec<String>,
        urgency_level: UrgencyLevel,
    ) -> Result<String, String> {
        if !self.config.enable_break_glass {
            return Err("Break glass is disabled".to_string());
        }

        // Check if we've exceeded the maximum active requests
        if self.active_requests.len() >= self.config.max_active_break_glass {
            return Err("Maximum active break glass requests exceeded".to_string());
        }

        // Validate justification requirement
        if self.config.require_justification && justification.is_none() {
            return Err("Justification is required for break glass requests".to_string());
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let expires_at = now + self.config.ttl_seconds;

        let request = BreakGlassRequest {
            request_id: format!("break_glass_{}_{}", session_id, now),
            session_id: session_id.clone(),
            user_id: user_id.clone(),
            reason,
            justification,
            requested_operations,
            requested_resources,
            urgency_level,
            created_at: now,
            expires_at,
            status: BreakGlassStatus::Pending,
            signatures: Vec::new(),
            metadata: HashMap::new(),
        };

        let request_id = request.request_id.clone();

        // Store request
        self.active_requests.insert(request_id.clone(), request);

        // Track user requests
        self.user_requests
            .entry(user_id)
            .or_insert_with(Vec::new)
            .push(request_id.clone());

        // Track session requests
        self.session_requests
            .entry(session_id)
            .or_insert_with(Vec::new)
            .push(request_id.clone());

        // Audit logging
        if self.config.audit_logging {
            self.log_audit_event("request_created", &request_id, &user_id);
        }

        Ok(request_id)
    }

    /// Add signature to break glass request
    pub fn add_signature(
        &mut self,
        request_id: &str,
        signer_id: String,
        signer_role: String,
        signature: String,
        justification: Option<String>,
    ) -> Result<(), String> {
        let request = self.active_requests
            .get_mut(request_id)
            .ok_or_else(|| format!("Break glass request {} not found", request_id))?;

        // Check if request is still pending
        if request.status != BreakGlassStatus::Pending {
            return Err("Request is no longer pending".to_string());
        }

        // Check if signer is authorized
        if !self.authorized_signers.contains(&signer_id) {
            return Err("Signer is not authorized".to_string());
        }

        // Check if signer has already signed
        if request.signatures.iter().any(|s| s.signer_id == signer_id) {
            return Err("Signer has already signed this request".to_string());
        }

        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let new_signature = BreakGlassSignature {
            signer_id,
            signer_role,
            signature,
            timestamp: now,
            justification,
            metadata: HashMap::new(),
        };

        request.signatures.push(new_signature);

        // Check if we have enough signatures
        if self.check_signature_threshold(request) {
            request.status = BreakGlassStatus::Approved;
            
            if self.config.audit_logging {
                self.log_audit_event("request_approved", request_id, &request.user_id);
            }
        }

        Ok(())
    }

    /// Check if signature threshold is met
    fn check_signature_threshold(&self, request: &BreakGlassRequest) -> bool {
        let (m, n) = self.config.m_of_n_threshold;
        let signature_count = request.signatures.len();
        
        signature_count >= m
    }

    /// Deny break glass request
    pub fn deny_request(&mut self, request_id: &str, reason: String) -> Result<(), String> {
        let request = self.active_requests
            .get_mut(request_id)
            .ok_or_else(|| format!("Break glass request {} not found", request_id))?;

        if request.status != BreakGlassStatus::Pending {
            return Err("Request is no longer pending".to_string());
        }

        request.status = BreakGlassStatus::Denied;
        request.metadata.insert("denial_reason".to_string(), reason);

        if self.config.audit_logging {
            self.log_audit_event("request_denied", request_id, &request.user_id);
        }

        Ok(())
    }

    /// Complete break glass request
    pub fn complete_request(&mut self, request_id: &str) -> Result<(), String> {
        let request = self.active_requests
            .get_mut(request_id)
            .ok_or_else(|| format!("Break glass request {} not found", request_id))?);

        if request.status != BreakGlassStatus::Approved {
            return Err("Request must be approved before completion".to_string());
        }

        request.status = BreakGlassStatus::Completed;

        if self.config.audit_logging {
            self.log_audit_event("request_completed", request_id, &request.user_id);
        }

        Ok(())
    }

    /// Check for expired requests and auto-page if needed
    pub fn check_expired_and_auto_page(&mut self) -> Vec<String> {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut expired_requests = Vec::new();
        let mut auto_paged_requests = Vec::new();

        for (request_id, request) in &mut self.active_requests {
            // Check for expired requests
            if now > request.expires_at {
                request.status = BreakGlassStatus::Expired;
                expired_requests.push(request_id.clone());
                continue;
            }

            // Check for auto-page threshold
            if self.config.auto_page_enabled && 
               request.status == BreakGlassStatus::Approved &&
               (now - request.created_at) > self.config.auto_page_threshold {
                request.status = BreakGlassStatus::AutoPaged;
                auto_paged_requests.push(request_id.clone());
                
                if self.config.audit_logging {
                    self.log_audit_event("auto_paged", request_id, &request.user_id);
                }
            }
        }

        // Clean up expired requests
        for request_id in &expired_requests {
            self.cleanup_request(request_id);
        }

        // Return auto-paged requests for notification
        auto_paged_requests
    }

    /// Clean up a request
    fn cleanup_request(&mut self, request_id: &str) {
        if let Some(request) = self.active_requests.remove(request_id) {
            // Remove from user requests
            if let Some(user_requests) = self.user_requests.get_mut(&request.user_id) {
                user_requests.retain(|id| id != request_id);
            }

            // Remove from session requests
            if let Some(session_requests) = self.session_requests.get_mut(&request.session_id) {
                session_requests.retain(|id| id != request_id);
            }
        }
    }

    /// Get request by ID
    pub fn get_request(&self, request_id: &str) -> Option<&BreakGlassRequest> {
        self.active_requests.get(request_id)
    }

    /// Get requests for user
    pub fn get_user_requests(&self, user_id: &str) -> Vec<&BreakGlassRequest> {
        if let Some(request_ids) = self.user_requests.get(user_id) {
            request_ids
                .iter()
                .filter_map(|id| self.active_requests.get(id))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Get requests for session
    pub fn get_session_requests(&self, session_id: &str) -> Vec<&BreakGlassRequest> {
        if let Some(request_ids) = self.session_requests.get(session_id) {
            request_ids
                .iter()
                .filter_map(|id| self.active_requests.get(id))
                .collect()
        } else {
            Vec::new()
        }
    }

    /// Get all active requests
    pub fn get_active_requests(&self) -> Vec<&BreakGlassRequest> {
        self.active_requests.values().collect()
    }

    /// Get manager statistics
    pub fn get_stats(&self) -> BreakGlassStats {
        let total_requests = self.active_requests.len();
        let pending_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::Pending)
            .count();
        let approved_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::Approved)
            .count();
        let denied_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::Denied)
            .count();
        let expired_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::Expired)
            .count();
        let auto_paged_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::AutoPaged)
            .count();
        let completed_requests = self.active_requests.values()
            .filter(|r| r.status == BreakGlassStatus::Completed)
            .count();

        BreakGlassStats {
            total_requests,
            pending_requests,
            approved_requests,
            denied_requests,
            expired_requests,
            auto_paged_requests,
            completed_requests,
            authorized_signers: self.authorized_signers.len(),
            config: self.config.clone(),
        }
    }

    /// Log audit event
    fn log_audit_event(&self, event_type: &str, request_id: &str, user_id: &str) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        println!(
            "[AUDIT] {} - Break Glass {} - Request: {}, User: {}",
            now,
            event_type,
            request_id,
            user_id
        );
    }

    /// Periodic cleanup
    pub fn periodic_cleanup(&mut self) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Only cleanup every hour
        if now - self.last_cleanup < 3600 {
            return;
        }

        self.check_expired_and_auto_page();
        self.last_cleanup = now;
    }
}

/// Break glass statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BreakGlassStats {
    pub total_requests: usize,
    pub pending_requests: usize,
    pub approved_requests: usize,
    pub denied_requests: usize,
    pub expired_requests: usize,
    pub auto_paged_requests: usize,
    pub completed_requests: usize,
    pub authorized_signers: usize,
    pub config: BreakGlassConfig,
}

/// Post-mortem stub for break glass usage
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PostMortemStub {
    pub request_id: String,
    pub session_id: String,
    pub user_id: String,
    pub operations_performed: Vec<String>,
    pub resources_accessed: Vec<String>,
    pub start_time: u64,
    pub end_time: u64,
    pub duration_seconds: u64,
    pub justification: Option<String>,
    pub audit_trail: Vec<String>,
    pub metadata: HashMap<String, String>,
}

impl PostMortemStub {
    /// Create new post-mortem stub
    pub fn new(request: &BreakGlassRequest) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            request_id: request.request_id.clone(),
            session_id: request.session_id.clone(),
            user_id: request.user_id.clone(),
            operations_performed: request.requested_operations.clone(),
            resources_accessed: request.requested_resources.clone(),
            start_time: request.created_at,
            end_time: now,
            duration_seconds: now - request.created_at,
            justification: request.justification.clone(),
            audit_trail: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// Add audit trail entry
    pub fn add_audit_entry(&mut self, entry: String) {
        self.audit_trail.push(entry);
    }

    /// Get stub hash for verification
    pub fn get_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(self.request_id.as_bytes());
        hasher.update(self.session_id.as_bytes());
        hasher.update(self.user_id.as_bytes());
        hasher.update(self.start_time.to_string().as_bytes());
        hasher.update(self.end_time.to_string().as_bytes());
        
        for operation in &self.operations_performed {
            hasher.update(operation.as_bytes());
        }
        
        format!("{:x}", hasher.finalize())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_urgency_level_parsing() {
        assert_eq!(UrgencyLevel::from_string("high").unwrap(), UrgencyLevel::High);
        assert_eq!(UrgencyLevel::from_string("emergency").unwrap(), UrgencyLevel::Emergency);
        assert!(UrgencyLevel::from_string("invalid").is_err());
    }

    #[test]
    fn test_urgency_level_comparison() {
        assert!(UrgencyLevel::High.numeric_value() > UrgencyLevel::Medium.numeric_value());
        assert!(UrgencyLevel::Emergency.numeric_value() > UrgencyLevel::Critical.numeric_value());
    }

    #[test]
    fn test_break_glass_request_creation() {
        let config = BreakGlassConfig::default();
        let mut manager = BreakGlassManager::new(config);

        let request_id = manager.create_request(
            "session1".to_string(),
            "user1".to_string(),
            "Emergency access needed".to_string(),
            Some("System failure requires immediate access".to_string()),
            vec!["read".to_string(), "write".to_string()],
            vec!["/critical/system".to_string()],
            UrgencyLevel::Emergency,
        ).unwrap();

        assert!(!request_id.is_empty());
        assert_eq!(manager.get_stats().total_requests, 1);
        assert_eq!(manager.get_stats().pending_requests, 1);
    }

    #[test]
    fn test_signature_threshold() {
        let mut config = BreakGlassConfig::default();
        config.m_of_n_threshold = (2, 3);
        let mut manager = BreakGlassManager::new(config);

        // Add authorized signers
        manager.add_authorized_signer("signer1".to_string());
        manager.add_authorized_signer("signer2".to_string());
        manager.add_authorized_signer("signer3".to_string());

        let request_id = manager.create_request(
            "session1".to_string(),
            "user1".to_string(),
            "Emergency access needed".to_string(),
            Some("Justification".to_string()),
            vec!["read".to_string()],
            vec!["/data".to_string()],
            UrgencyLevel::High,
        ).unwrap();

        // First signature should not approve
        manager.add_signature(
            &request_id,
            "signer1".to_string(),
            "admin".to_string(),
            "signature1".to_string(),
            None,
        ).unwrap();

        let request = manager.get_request(&request_id).unwrap();
        assert_eq!(request.status, BreakGlassStatus::Pending);

        // Second signature should approve
        manager.add_signature(
            &request_id,
            "signer2".to_string(),
            "admin".to_string(),
            "signature2".to_string(),
            None,
        ).unwrap();

        let request = manager.get_request(&request_id).unwrap();
        assert_eq!(request.status, BreakGlassStatus::Approved);
    }

    #[test]
    fn test_justification_requirement() {
        let mut config = BreakGlassConfig::default();
        config.require_justification = true;
        let mut manager = BreakGlassManager::new(config);

        let result = manager.create_request(
            "session1".to_string(),
            "user1".to_string(),
            "Emergency access needed".to_string(),
            None, // No justification
            vec!["read".to_string()],
            vec!["/data".to_string()],
            UrgencyLevel::High,
        );

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Justification is required"));
    }

    #[test]
    fn test_duplicate_signature_prevention() {
        let config = BreakGlassConfig::default();
        let mut manager = BreakGlassManager::new(config);

        manager.add_authorized_signer("signer1".to_string());

        let request_id = manager.create_request(
            "session1".to_string(),
            "user1".to_string(),
            "Emergency access needed".to_string(),
            Some("Justification".to_string()),
            vec!["read".to_string()],
            vec!["/data".to_string()],
            UrgencyLevel::High,
        ).unwrap();

        // First signature
        manager.add_signature(
            &request_id,
            "signer1".to_string(),
            "admin".to_string(),
            "signature1".to_string(),
            None,
        ).unwrap();

        // Duplicate signature should fail
        let result = manager.add_signature(
            &request_id,
            "signer1".to_string(),
            "admin".to_string(),
            "signature2".to_string(),
            None,
        );

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("already signed"));
    }

    #[test]
    fn test_post_mortem_stub() {
        let config = BreakGlassConfig::default();
        let mut manager = BreakGlassManager::new(config);

        let request_id = manager.create_request(
            "session1".to_string(),
            "user1".to_string(),
            "Emergency access needed".to_string(),
            Some("Justification".to_string()),
            vec!["read".to_string()],
            vec!["/data".to_string()],
            UrgencyLevel::High,
        ).unwrap();

        let request = manager.get_request(&request_id).unwrap();
        let stub = PostMortemStub::new(request);

        assert_eq!(stub.request_id, request_id);
        assert_eq!(stub.user_id, "user1");
        assert_eq!(stub.operations_performed.len(), 1);
        assert_eq!(stub.resources_accessed.len(), 1);

        let hash = stub.get_hash();
        assert!(!hash.is_empty());
    }

    #[test]
    fn test_concurrency_stress() {
        let mut config = BreakGlassConfig::default();
        config.max_active_break_glass = 100;
        let mut manager = BreakGlassManager::new(config);

        // Create many requests to stress test the manager
        for i in 0..100 {
            let request_id = manager.create_request(
                format!("session_{}", i),
                format!("user_{}", i),
                format!("Request {}", i),
                Some("Justification".to_string()),
                vec!["read".to_string()],
                vec![format!("/data_{}", i)],
                UrgencyLevel::Medium,
            ).unwrap();

            assert!(!request_id.is_empty());
        }

        let stats = manager.get_stats();
        assert_eq!(stats.total_requests, 100);
        assert_eq!(stats.pending_requests, 100);

        // Try to create one more - should fail
        let result = manager.create_request(
            "session_101".to_string(),
            "user_101".to_string(),
            "Request 101".to_string(),
            Some("Justification".to_string()),
            vec!["read".to_string()],
            vec!["/data_101".to_string()],
            UrgencyLevel::Medium,
        );

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Maximum active break glass requests exceeded"));
    }
}
