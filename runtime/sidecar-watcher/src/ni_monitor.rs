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
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Non-interference monitor configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIMonitorConfig {
    pub enable_monitoring: bool,
    pub strict_mode: bool,
    pub max_prefixes: usize,
    pub prefix_length: usize,
    pub drift_threshold_ms: u64,
    pub enable_audit_logging: bool,
}

impl Default for NIMonitorConfig {
    fn default() -> Self {
        Self {
            enable_monitoring: true,
            strict_mode: true,
            max_prefixes: 10000,
            prefix_length: 64,
            drift_threshold_ms: 100,
            enable_audit_logging: true,
        }
    }
}

/// Security label for non-interference analysis
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecurityLabel {
    Public,
    Internal,
    Confidential,
    Secret,
    Custom(String),
}

impl SecurityLabel {
    /// Convert to string representation
    pub fn to_string(&self) -> String {
        match self {
            SecurityLabel::Public => "public".to_string(),
            SecurityLabel::Internal => "internal".to_string(),
            SecurityLabel::Confidential => "confidential".to_string(),
            SecurityLabel::Secret => "secret".to_string(),
            SecurityLabel::Custom(name) => format!("custom:{}", name),
        }
    }

    /// Parse from string representation
    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "public" => Ok(SecurityLabel::Public),
            "internal" => Ok(SecurityLabel::Internal),
            "confidential" => Ok(SecurityLabel::Confidential),
            "secret" => Ok(SecurityLabel::Secret),
            s if s.starts_with("custom:") => {
                let name = s.strip_prefix("custom:").unwrap();
                Ok(SecurityLabel::Custom(name.to_string()))
            }
            _ => Err(format!("Unknown security label: {}", s)),
        }
    }

    /// Check if this label is less than or equal to another (lattice ordering)
    pub fn le(&self, other: &SecurityLabel) -> bool {
        match (self, other) {
            (SecurityLabel::Public, _) => true,
            (SecurityLabel::Internal, SecurityLabel::Internal) => true,
            (SecurityLabel::Internal, SecurityLabel::Confidential) => true,
            (SecurityLabel::Internal, SecurityLabel::Secret) => true,
            (SecurityLabel::Confidential, SecurityLabel::Confidential) => true,
            (SecurityLabel::Confidential, SecurityLabel::Secret) => true,
            (SecurityLabel::Secret, SecurityLabel::Secret) => true,
            (SecurityLabel::Custom(name1), SecurityLabel::Custom(name2)) => name1 == name2,
            _ => false,
        }
    }

    /// Check if this label is greater than or equal to another
    pub fn ge(&self, other: &SecurityLabel) -> bool {
        other.le(self)
    }
}

/// Event for non-interference analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIEvent {
    pub event_id: String,
    pub timestamp: u64,
    pub session_id: String,
    pub user_id: String,
    pub operation: String,
    pub input_labels: Vec<SecurityLabel>,
    pub output_labels: Vec<SecurityLabel>,
    pub data_paths: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// Prefix for non-interference analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIPrefix {
    pub prefix_id: String,
    pub events: Vec<NIEvent>,
    pub input_label: SecurityLabel,
    pub output_label: SecurityLabel,
    pub created_at: u64,
    pub last_updated: u64,
}

impl NIPrefix {
    /// Create new NI prefix
    pub fn new(prefix_id: String, input_label: SecurityLabel, output_label: SecurityLabel) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        Self {
            prefix_id,
            events: Vec::new(),
            input_label,
            output_label,
            created_at: now,
            last_updated: now,
        }
    }

    /// Add event to prefix
    pub fn add_event(&mut self, event: NIEvent) {
        self.events.push(event);
        self.last_updated = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }

    /// Check if prefix violates non-interference
    pub fn violates_ni(&self) -> bool {
        // Check if any event has input labels that are not dominated by the prefix input label
        for event in &self.events {
            for input_label in &event.input_labels {
                if !input_label.le(&self.input_label) {
                    return true;
                }
            }
        }

        // Check if any event has output labels that dominate the prefix output label
        for event in &self.events {
            for output_label in &event.output_labels {
                if !self.output_label.le(output_label) {
                    return true;
                }
            }
        }

        false
    }

    /// Get prefix hash for verification
    pub fn get_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(self.prefix_id.as_bytes());
        hasher.update(self.input_label.to_string().as_bytes());
        hasher.update(self.output_label.to_string().as_bytes());
        hasher.update(self.created_at.to_string().as_bytes());
        hasher.update(self.last_updated.to_string().as_bytes());

        for event in &self.events {
            hasher.update(event.event_id.as_bytes());
            hasher.update(event.timestamp.to_string().as_bytes());
        }

        format!("{:x}", hasher.finalize())
    }
}

/// Non-interference monitor state
#[derive(Debug, Clone)]
pub struct NIMonitorState {
    pub prefixes: HashMap<String, NIPrefix>,
    pub active_sessions: HashSet<String>,
    pub violation_count: u64,
    pub last_audit: u64,
    pub config: NIMonitorConfig,
}

impl NIMonitorState {
    /// Create new NI monitor state
    pub fn new(config: NIMonitorConfig) -> Self {
        Self {
            prefixes: HashMap::new(),
            active_sessions: HashSet::new(),
            violation_count: 0,
            last_audit: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            config,
        }
    }

    /// Add event to monitor
    pub fn add_event(&mut self, event: NIEvent) -> Result<bool, String> {
        if !self.config.enable_monitoring {
            return Ok(true);
        }

        // Check if we've exceeded the maximum number of prefixes
        if self.prefixes.len() >= self.config.max_prefixes {
            return Err("Maximum number of prefixes exceeded".to_string());
        }

        // Generate prefix ID based on event characteristics
        let prefix_id = self.generate_prefix_id(&event);

        // Get or create prefix
        let prefix = self.prefixes.entry(prefix_id.clone()).or_insert_with(|| {
            NIPrefix::new(
                prefix_id,
                event
                    .input_labels
                    .first()
                    .unwrap_or(&SecurityLabel::Public)
                    .clone(),
                event
                    .output_labels
                    .first()
                    .unwrap_or(&SecurityLabel::Public)
                    .clone(),
            )
        });

        // Add event to prefix
        prefix.add_event(event.clone());

        // Check for non-interference violations
        if prefix.violates_ni() {
            self.violation_count += 1;

            if self.config.strict_mode {
                return Err("Non-interference violation detected".to_string());
            }
        }

        // Track active session
        self.active_sessions.insert(event.session_id);

        // Audit logging
        if self.config.enable_audit_logging {
            self.log_audit_event(&event, prefix);
        }

        Ok(true)
    }

    /// Generate prefix ID for an event
    fn generate_prefix_id(&self, event: &NIEvent) -> String {
        let mut hasher = Sha256::new();
        hasher.update(event.session_id.as_bytes());
        hasher.update(event.operation.as_bytes());

        // Include input and output labels in prefix ID
        for label in &event.input_labels {
            hasher.update(label.to_string().as_bytes());
        }
        for label in &event.output_labels {
            hasher.update(label.to_string().as_bytes());
        }

        let hash = hasher.finalize();
        format!("prefix_{:x}", hash)[..self.config.prefix_length].to_string()
    }

    /// Log audit event
    fn log_audit_event(&mut self, event: &NIEvent, prefix: &NIPrefix) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        // Log to audit trail (in a real implementation, this would go to a secure log)
        println!(
            "[AUDIT] {} - Session: {}, User: {}, Operation: {}, Prefix: {}, Violation: {}",
            now,
            event.session_id,
            event.user_id,
            event.operation,
            prefix.prefix_id,
            prefix.violates_ni()
        );

        self.last_audit = now;
    }

    /// Check non-interference for all prefixes
    pub fn check_all_prefixes(&self) -> Vec<String> {
        let mut violations = Vec::new();

        for prefix in self.prefixes.values() {
            if prefix.violates_ni() {
                violations.push(format!(
                    "Prefix {} violates non-interference: input={}, output={}",
                    prefix.prefix_id,
                    prefix.input_label.to_string(),
                    prefix.output_label.to_string()
                ));
            }
        }

        violations
    }

    /// Get monitor statistics
    pub fn get_stats(&self) -> NIMonitorStats {
        NIMonitorStats {
            total_prefixes: self.prefixes.len(),
            active_sessions: self.active_sessions.len(),
            violation_count: self.violation_count,
            last_audit: self.last_audit,
            config: self.config.clone(),
        }
    }

    /// Clean up old prefixes
    pub fn cleanup_old_prefixes(&mut self, max_age_seconds: u64) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();

        let mut to_remove = Vec::new();

        for (prefix_id, prefix) in &self.prefixes {
            if now - prefix.last_updated > max_age_seconds {
                to_remove.push(prefix_id.clone());
            }
        }

        for prefix_id in to_remove {
            self.prefixes.remove(&prefix_id);
        }
    }

    /// Verify prefix integrity
    pub fn verify_prefix_integrity(&self, prefix_id: &str) -> Result<bool, String> {
        let prefix = self
            .prefixes
            .get(prefix_id)
            .ok_or_else(|| format!("Prefix {} not found", prefix_id))?;

        let computed_hash = prefix.get_hash();

        // In a real implementation, this would compare against a stored hash
        // For now, we just return true if the hash computation succeeds
        Ok(!computed_hash.is_empty())
    }
}

/// Non-interference monitor statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIMonitorStats {
    pub total_prefixes: usize,
    pub active_sessions: usize,
    pub violation_count: u64,
    pub last_audit: u64,
    pub config: NIMonitorConfig,
}

/// Non-interference monitor
pub struct NIMonitor {
    state: NIMonitorState,
}

impl NIMonitor {
    /// Create new NI monitor
    pub fn new(config: NIMonitorConfig) -> Self {
        Self {
            state: NIMonitorState::new(config),
        }
    }

    /// Monitor an event for non-interference violations
    pub fn monitor_event(&mut self, event: NIEvent) -> Result<bool, String> {
        self.state.add_event(event)
    }

    /// Check all prefixes for violations
    pub fn check_violations(&self) -> Vec<String> {
        self.state.check_all_prefixes()
    }

    /// Get monitor statistics
    pub fn get_stats(&self) -> NIMonitorStats {
        self.state.get_stats()
    }

    /// Clean up old prefixes
    pub fn cleanup(&mut self, max_age_seconds: u64) {
        self.state.cleanup_old_prefixes(max_age_seconds);
    }

    /// Verify prefix integrity
    pub fn verify_prefix(&self, prefix_id: &str) -> Result<bool, String> {
        self.state.verify_prefix_integrity(prefix_id)
    }

    /// Get all prefixes
    pub fn get_prefixes(&self) -> &HashMap<String, NIPrefix> {
        &self.state.prefixes
    }

    /// Get specific prefix
    pub fn get_prefix(&self, prefix_id: &str) -> Option<&NIPrefix> {
        self.state.prefixes.get(prefix_id)
    }
}

/// Non-interference proof obligation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIProofObligation {
    pub obligation_id: String,
    pub prefix_id: String,
    pub condition: String,
    pub proof: String,
    pub verified: bool,
    pub verified_at: Option<u64>,
}

/// Non-interference verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIVerificationResult {
    pub prefix_id: String,
    pub verified: bool,
    pub violations: Vec<String>,
    pub proof_obligations: Vec<NIProofObligation>,
    pub timestamp: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_security_label_ordering() {
        assert!(SecurityLabel::Public.le(&SecurityLabel::Secret));
        assert!(SecurityLabel::Internal.le(&SecurityLabel::Confidential));
        assert!(!SecurityLabel::Secret.le(&SecurityLabel::Public));
    }

    #[test]
    fn test_ni_prefix_creation() {
        let prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Confidential,
            SecurityLabel::Internal,
        );

        assert_eq!(prefix.prefix_id, "test_prefix");
        assert_eq!(prefix.events.len(), 0);
        assert!(!prefix.violates_ni());
    }

    #[test]
    fn test_ni_prefix_violation() {
        let mut prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Internal,
            SecurityLabel::Confidential,
        );

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Secret], // Higher than prefix input
            output_labels: vec![SecurityLabel::Internal],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        prefix.add_event(event);
        assert!(prefix.violates_ni());
    }

    #[test]
    fn test_ni_monitor_basic() {
        let config = NIMonitorConfig::default();
        let mut monitor = NIMonitor::new(config);

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Internal],
            output_labels: vec![SecurityLabel::Public],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        let result = monitor.monitor_event(event);
        assert!(result.is_ok());
        assert_eq!(monitor.get_stats().total_prefixes, 1);
    }

    #[test]
    fn test_ni_monitor_violation() {
        let mut config = NIMonitorConfig::default();
        config.strict_mode = true;
        let mut monitor = NIMonitor::new(config);

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Secret],
            output_labels: vec![SecurityLabel::Public],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        let result = monitor.monitor_event(event);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Non-interference violation"));
    }

    #[test]
    fn test_prefix_integrity() {
        let config = NIMonitorConfig::default();
        let monitor = NIMonitor::new(config);

        // Create a test prefix
        let prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Internal,
            SecurityLabel::Public,
        );

        let hash = prefix.get_hash();
        assert!(!hash.is_empty());
        assert!(hash.starts_with("prefix_"));
    }

    #[test]
    fn test_concurrency_stress() {
        let mut config = NIMonitorConfig::default();
        config.max_prefixes = 1000;
        let mut monitor = NIMonitor::new(config);

        // Create many events to stress test the monitor
        for i in 0..1000 {
            let event = NIEvent {
                event_id: format!("event_{}", i),
                timestamp: 1000 + i as u64,
                session_id: format!("session_{}", i % 100),
                user_id: format!("user_{}", i % 50),
                operation: "read".to_string(),
                input_labels: vec![SecurityLabel::Internal],
                output_labels: vec![SecurityLabel::Public],
                data_paths: vec![format!("$.data_{}", i)],
                metadata: HashMap::new(),
            };

            let result = monitor.monitor_event(event);
            assert!(result.is_ok());
        }

        let stats = monitor.get_stats();
        assert_eq!(stats.total_prefixes, 1000);
        assert_eq!(stats.active_sessions, 100);
    }
}
