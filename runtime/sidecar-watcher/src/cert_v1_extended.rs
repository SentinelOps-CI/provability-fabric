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
use std::collections::HashMap;

use crate::time_util;
use super::cert_v1_core::CertV1Core;

/// CERT-V1 Extended Certificate (Async)
///
/// Rich certificate containing comprehensive reasoning, blocked spans, and detector statistics.
/// This is generated asynchronously after the core certificate for detailed analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertV1Extended {
    /// Core certificate data
    pub core: CertV1Core,

    /// Full reasoning for the decision
    pub reasoning: DecisionReasoning,

    /// Blocked spans information
    pub blocked_spans: Vec<BlockedSpan>,

    /// Detector statistics
    pub detector_stats: DetectorStats,

    /// Additional metadata
    pub metadata: ExtendedMetadata,
}

/// Decision reasoning details
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionReasoning {
    /// Primary decision reason
    pub primary_reason: String,

    /// Detailed explanation
    pub explanation: String,

    /// Applied rules
    pub applied_rules: Vec<AppliedRule>,

    /// Policy references
    pub policy_references: Vec<PolicyReference>,

    /// Confidence score (0.0 to 1.0)
    pub confidence: f64,

    /// Decision factors
    pub factors: Vec<DecisionFactor>,
}

/// Applied rule information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppliedRule {
    /// Rule identifier
    pub rule_id: String,

    /// Rule description
    pub description: String,

    /// Rule type
    pub rule_type: String,

    /// Whether rule matched
    pub matched: bool,

    /// Rule priority
    pub priority: u32,

    /// Rule conditions
    pub conditions: Vec<String>,
}

/// Policy reference
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyReference {
    /// Policy identifier
    pub policy_id: String,

    /// Policy version
    pub version: String,

    /// Policy section
    pub section: String,

    /// Reference text
    pub reference_text: String,
}

/// Decision factor
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DecisionFactor {
    /// Factor name
    pub name: String,

    /// Factor value
    pub value: String,

    /// Factor weight
    pub weight: f64,

    /// Factor impact
    pub impact: String, // "positive", "negative", "neutral"
}

/// Blocked span information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockedSpan {
    /// Span identifier
    pub span_id: String,

    /// Start position
    pub start: usize,

    /// End position
    pub end: usize,

    /// Block reason
    pub reason: String,

    /// Block type
    pub block_type: String, // "pii", "secret", "malicious", "policy_violation"

    /// Confidence score
    pub confidence: f64,

    /// Original content (if safe to store)
    pub original_content: Option<String>,

    /// Replacement content
    pub replacement_content: Option<String>,
}

/// Detector statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct DetectorStats {
    /// PII detection stats
    pub pii_stats: PIIStats,

    /// Secret detection stats
    pub secret_stats: SecretStats,

    /// Malicious content stats
    pub malicious_stats: MaliciousStats,

    /// Policy violation stats
    pub policy_violation_stats: PolicyViolationStats,

    /// Overall detection summary
    pub summary: DetectionSummary,
}

/// PII detection statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PIIStats {
    /// Number of PII detections
    pub detections: u32,

    /// PII types detected
    pub types_detected: Vec<String>,

    /// Confidence scores
    pub confidence_scores: Vec<f64>,

    /// False positive rate
    pub false_positive_rate: f64,
}

/// Secret detection statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecretStats {
    /// Number of secret detections
    pub detections: u32,

    /// Secret types detected
    pub types_detected: Vec<String>,

    /// Confidence scores
    pub confidence_scores: Vec<f64>,

    /// False positive rate
    pub false_positive_rate: f64,
}

/// Malicious content statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MaliciousStats {
    /// Number of malicious detections
    pub detections: u32,

    /// Threat types detected
    pub threat_types: Vec<String>,

    /// Severity scores
    pub severity_scores: Vec<f64>,

    /// False positive rate
    pub false_positive_rate: f64,
}

/// Policy violation statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyViolationStats {
    /// Number of policy violations
    pub violations: u32,

    /// Violation types
    pub violation_types: Vec<String>,

    /// Severity scores
    pub severity_scores: Vec<f64>,

    /// Compliance rate
    pub compliance_rate: f64,
}

/// Detection summary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectionSummary {
    /// Total detections
    pub total_detections: u32,

    /// High confidence detections
    pub high_confidence: u32,

    /// Medium confidence detections
    pub medium_confidence: u32,

    /// Low confidence detections
    pub low_confidence: u32,

    /// Overall risk score
    pub risk_score: f64,

    /// Recommended action
    pub recommended_action: String,
}

/// Extended metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtendedMetadata {
    /// Generation timestamp
    pub generated_at: u64,

    /// Processing time in milliseconds
    pub processing_time_ms: u64,

    /// Sidecar build information
    pub sidecar_build: String,

    /// Environment information
    pub environment: HashMap<String, String>,

    /// Additional context
    pub context: HashMap<String, String>,

    /// Version information
    pub version: String,
}

impl CertV1Extended {
    /// Create a new extended certificate from a core certificate
    pub fn from_core(core: CertV1Core) -> Self {
        let now = time_util::unix_secs();

        Self {
            core,
            reasoning: DecisionReasoning::default(),
            blocked_spans: Vec::new(),
            detector_stats: DetectorStats::default(),
            metadata: ExtendedMetadata {
                generated_at: now,
                processing_time_ms: 0,
                sidecar_build: String::new(),
                environment: HashMap::new(),
                context: HashMap::new(),
                version: "1.0.0".to_string(),
            },
        }
    }

    /// Add reasoning information
    pub fn add_reasoning(&mut self, reasoning: DecisionReasoning) {
        self.reasoning = reasoning;
    }

    /// Add blocked span
    pub fn add_blocked_span(&mut self, span: BlockedSpan) {
        self.blocked_spans.push(span);
    }

    /// Set detector statistics
    pub fn set_detector_stats(&mut self, stats: DetectorStats) {
        self.detector_stats = stats;
    }

    /// Update metadata
    pub fn update_metadata(&mut self, metadata: ExtendedMetadata) {
        self.metadata = metadata;
    }

    /// Get total size in bytes
    pub fn size_bytes(&self) -> usize {
        self.core.size_bytes() + serde_json::to_string(self).unwrap_or_default().len()
    }

    /// Convert to JSON for storage/transmission
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }

    /// Create from JSON
    pub fn from_json(json: &str) -> Result<Self, serde_json::Error> {
        serde_json::from_str(json)
    }
}

impl Default for DecisionReasoning {
    fn default() -> Self {
        Self {
            primary_reason: String::new(),
            explanation: String::new(),
            applied_rules: Vec::new(),
            policy_references: Vec::new(),
            confidence: 0.0,
            factors: Vec::new(),
        }
    }
}


impl Default for PIIStats {
    fn default() -> Self {
        Self {
            detections: 0,
            types_detected: Vec::new(),
            confidence_scores: Vec::new(),
            false_positive_rate: 0.0,
        }
    }
}

impl Default for SecretStats {
    fn default() -> Self {
        Self {
            detections: 0,
            types_detected: Vec::new(),
            confidence_scores: Vec::new(),
            false_positive_rate: 0.0,
        }
    }
}

impl Default for MaliciousStats {
    fn default() -> Self {
        Self {
            detections: 0,
            threat_types: Vec::new(),
            severity_scores: Vec::new(),
            false_positive_rate: 0.0,
        }
    }
}

impl Default for PolicyViolationStats {
    fn default() -> Self {
        Self {
            violations: 0,
            violation_types: Vec::new(),
            severity_scores: Vec::new(),
            compliance_rate: 1.0,
        }
    }
}

impl Default for DetectionSummary {
    fn default() -> Self {
        Self {
            total_detections: 0,
            high_confidence: 0,
            medium_confidence: 0,
            low_confidence: 0,
            risk_score: 0.0,
            recommended_action: "none".to_string(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extended_cert_creation() {
        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let extended = CertV1Extended::from_core(core);

        assert_eq!(extended.core.bundle_id, "bundle-123");
        assert_eq!(extended.core.ni_monitor, "accept");
        assert!(extended.blocked_spans.is_empty());
    }

    #[test]
    fn test_extended_cert_reasoning() {
        let core = CertV1Core::default();
        let mut extended = CertV1Extended::from_core(core);

        let reasoning = DecisionReasoning {
            primary_reason: "Policy compliance".to_string(),
            explanation: "All checks passed".to_string(),
            applied_rules: vec![AppliedRule {
                rule_id: "rule-1".to_string(),
                description: "Allow if authorized".to_string(),
                rule_type: "authorization".to_string(),
                matched: true,
                priority: 1,
                conditions: vec!["user.role == 'admin'".to_string()],
            }],
            policy_references: Vec::new(),
            confidence: 0.95,
            factors: Vec::new(),
        };

        extended.add_reasoning(reasoning);

        assert_eq!(extended.reasoning.primary_reason, "Policy compliance");
        assert_eq!(extended.reasoning.confidence, 0.95);
        assert_eq!(extended.reasoning.applied_rules.len(), 1);
    }

    #[test]
    fn test_extended_cert_blocked_spans() {
        let core = CertV1Core::default();
        let mut extended = CertV1Extended::from_core(core);

        let span = BlockedSpan {
            span_id: "span-1".to_string(),
            start: 0,
            end: 10,
            reason: "PII detected".to_string(),
            block_type: "pii".to_string(),
            confidence: 0.9,
            original_content: Some("John Doe".to_string()),
            replacement_content: Some("[REDACTED]".to_string()),
        };

        extended.add_blocked_span(span);

        assert_eq!(extended.blocked_spans.len(), 1);
        assert_eq!(extended.blocked_spans[0].span_id, "span-1");
        assert_eq!(extended.blocked_spans[0].block_type, "pii");
    }

    #[test]
    fn test_extended_cert_json_serialization() {
        let core = CertV1Core::new(
            "bundle-123".to_string(),
            1,
            "policy-hash-456".to_string(),
            "proof-hash-789".to_string(),
            "automata-hash-abc".to_string(),
            "labeler-hash-def".to_string(),
            "accept".to_string(),
            42,
            "PERMIT".to_string(),
            "tenant-1".to_string(),
            "session-1".to_string(),
        );

        let extended = CertV1Extended::from_core(core);
        let json = extended.to_json().unwrap();
        let deserialized = CertV1Extended::from_json(&json).unwrap();

        assert_eq!(extended.core.bundle_id, deserialized.core.bundle_id);
        assert_eq!(extended.core.ni_monitor, deserialized.core.ni_monitor);
    }
}
