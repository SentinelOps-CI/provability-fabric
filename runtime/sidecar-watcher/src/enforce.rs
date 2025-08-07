// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::RwLock;
use tracing::{error, info, warn};
use uuid::Uuid;

/// Represents a kernel decision that must be validated
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KernelDecision {
    pub decision_id: String,
    pub session_id: String,
    pub resource: String,
    pub capability: String,
    pub decision: DecisionType,
    pub reasoning: String,
    pub risk_score: f64,
    pub timestamp: String,
    pub evidence_hash: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum DecisionType {
    Allow,
    Deny,
    Quarantine,
    Escalate,
}

/// Represents a tool call that requires validation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolCall {
    pub call_id: String,
    pub session_id: String,
    pub tool_name: String,
    pub parameters: HashMap<String, serde_json::Value>,
    pub risk_score: f64,
    pub kernel_decision: Option<KernelDecision>,
    pub timestamp: String,
}

/// Represents an approval request for high-risk operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApprovalRequest {
    pub request_id: String,
    pub session_id: String,
    pub tool_call: ToolCall,
    pub risk_score: f64,
    pub reason: String,
    pub created_at: String,
    pub expires_at: String,
    pub status: ApprovalStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ApprovalStatus {
    Pending,
    Approved,
    Denied,
    Expired,
}

/// Represents a violation that occurred
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Violation {
    pub violation_id: String,
    pub session_id: String,
    pub violation_type: ViolationType,
    pub reason: String,
    pub timestamp: String,
    pub tool_call: Option<ToolCall>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ViolationType {
    NoDecision,
    InvalidDecision,
    RiskThresholdExceeded,
    UnauthorizedTool,
    CrossTenantAccess,
    PrivacyViolation,
}

/// Configuration for enforcement mode
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnforcementConfig {
    pub risk_threshold: f64,
    pub approval_timeout_minutes: u32,
    pub deny_by_default: bool,
    pub require_kernel_decision: bool,
    pub enable_human_approval: bool,
    pub broker_endpoint: String,
}

impl Default for EnforcementConfig {
    fn default() -> Self {
        Self {
            risk_threshold: 0.7,
            approval_timeout_minutes: 30,
            deny_by_default: true,
            require_kernel_decision: true,
            enable_human_approval: true,
            broker_endpoint: "http://localhost:8083".to_string(),
        }
    }
}

/// Main enforcement engine
pub struct EnforcementEngine {
    config: EnforcementConfig,
    pending_approvals: Arc<RwLock<HashMap<String, ApprovalRequest>>>,
    violations: Arc<RwLock<Vec<Violation>>>,
    http_client: reqwest::Client,
}

impl EnforcementEngine {
    pub fn new(config: EnforcementConfig) -> Result<Self> {
        let http_client = reqwest::Client::builder()
            .timeout(std::time::Duration::from_secs(30))
            .build()
            .context("Failed to create HTTP client")?;

        Ok(Self {
            config,
            pending_approvals: Arc::new(RwLock::new(HashMap::new())),
            violations: Arc::new(RwLock::new(Vec::new())),
            http_client,
        })
    }

    /// Validate a tool call and determine if it should be allowed
    pub async fn validate_tool_call(&self, tool_call: ToolCall) -> Result<ValidationResult> {
        info!("Validating tool call: {}", tool_call.call_id);

        // Check if kernel decision is required and present
        if self.config.require_kernel_decision {
            match &tool_call.kernel_decision {
                None => {
                    let violation = Violation {
                        violation_id: Uuid::new_v4().to_string(),
                        session_id: tool_call.session_id.clone(),
                        violation_type: ViolationType::NoDecision,
                        reason: "No kernel decision provided".to_string(),
                        timestamp: chrono::Utc::now().to_rfc3339(),
                        tool_call: Some(tool_call.clone()),
                    };
                    self.record_violation(violation).await;
                    return Ok(ValidationResult::Denied("No kernel decision".to_string()));
                }
                Some(decision) => {
                    if !self.validate_kernel_decision(decision).await? {
                        let violation = Violation {
                            violation_id: Uuid::new_v4().to_string(),
                            session_id: tool_call.session_id.clone(),
                            violation_type: ViolationType::InvalidDecision,
                            reason: "Invalid kernel decision".to_string(),
                            timestamp: chrono::Utc::now().to_rfc3339(),
                            tool_call: Some(tool_call.clone()),
                        };
                        self.record_violation(violation).await;
                        return Ok(ValidationResult::Denied("Invalid kernel decision".to_string()));
                    }
                }
            }
        }

        // Check risk threshold
        if tool_call.risk_score >= self.config.risk_threshold {
            if self.config.enable_human_approval {
                return self.create_approval_request(tool_call).await;
            } else {
                let violation = Violation {
                    violation_id: Uuid::new_v4().to_string(),
                    session_id: tool_call.session_id.clone(),
                    violation_type: ViolationType::RiskThresholdExceeded,
                    reason: format!("Risk score {} exceeds threshold {}", 
                                  tool_call.risk_score, self.config.risk_threshold),
                    timestamp: chrono::Utc::now().to_rfc3339(),
                    tool_call: Some(tool_call.clone()),
                };
                self.record_violation(violation).await;
                return Ok(ValidationResult::Denied("Risk threshold exceeded".to_string()));
            }
        }

        // Check for unauthorized tools
        if !self.is_tool_authorized(&tool_call).await? {
            let violation = Violation {
                violation_id: Uuid::new_v4().to_string(),
                session_id: tool_call.session_id.clone(),
                violation_type: ViolationType::UnauthorizedTool,
                reason: format!("Tool {} not authorized", tool_call.tool_name),
                timestamp: chrono::Utc::now().to_rfc3339(),
                tool_call: Some(tool_call.clone()),
            };
            self.record_violation(violation).await;
            return Ok(ValidationResult::Denied("Unauthorized tool".to_string()));
        }

        // Check for cross-tenant access
        if self.detect_cross_tenant_access(&tool_call).await? {
            let violation = Violation {
                violation_id: Uuid::new_v4().to_string(),
                session_id: tool_call.session_id.clone(),
                violation_type: ViolationType::CrossTenantAccess,
                reason: "Cross-tenant access detected".to_string(),
                timestamp: chrono::Utc::now().to_rfc3339(),
                tool_call: Some(tool_call.clone()),
            };
            self.record_violation(violation).await;
            return Ok(ValidationResult::Denied("Cross-tenant access denied".to_string()));
        }

        // Check for privacy violations
        if self.detect_privacy_violation(&tool_call).await? {
            let violation = Violation {
                violation_id: Uuid::new_v4().to_string(),
                session_id: tool_call.session_id.clone(),
                violation_type: ViolationType::PrivacyViolation,
                reason: "Privacy violation detected".to_string(),
                timestamp: chrono::Utc::now().to_rfc3339(),
                tool_call: Some(tool_call.clone()),
            };
            self.record_violation(violation).await;
            return Ok(ValidationResult::Denied("Privacy violation".to_string()));
        }

        // If deny by default is enabled, only allow if explicitly approved
        if self.config.deny_by_default {
            return Ok(ValidationResult::Denied("Deny by default".to_string()));
        }

        Ok(ValidationResult::Allowed)
    }

    /// Validate a kernel decision
    async fn validate_kernel_decision(&self, decision: &KernelDecision) -> Result<bool> {
        // Check if decision is recent (within last 5 minutes)
        let decision_time = chrono::DateTime::parse_from_rfc3339(&decision.timestamp)
            .context("Invalid decision timestamp")?;
        let now = chrono::Utc::now();
        let age = now.signed_duration_since(decision_time);
        
        if age.num_minutes() > 5 {
            warn!("Kernel decision too old: {} minutes", age.num_minutes());
            return Ok(false);
        }

        // Check if decision is valid (has evidence hash)
        if decision.evidence_hash.is_empty() {
            warn!("Kernel decision missing evidence hash");
            return Ok(false);
        }

        // Check if decision type is valid
        match decision.decision {
            DecisionType::Allow => Ok(true),
            DecisionType::Deny => Ok(false),
            DecisionType::Quarantine => Ok(false),
            DecisionType::Escalate => {
                // Escalated decisions require additional validation
                self.validate_escalated_decision(decision).await
            }
        }
    }

    /// Validate an escalated decision
    async fn validate_escalated_decision(&self, decision: &KernelDecision) -> Result<bool> {
        // For escalated decisions, check with the broker
        let response = self.http_client
            .post(&format!("{}/api/validate-escalation", self.config.broker_endpoint))
            .json(decision)
            .send()
            .await
            .context("Failed to validate escalation")?;

        if response.status().is_success() {
            let result: serde_json::Value = response.json().await
                .context("Failed to parse escalation response")?;
            Ok(result.get("approved").and_then(|v| v.as_bool()).unwrap_or(false))
        } else {
            warn!("Escalation validation failed: {}", response.status());
            Ok(false)
        }
    }

    /// Check if a tool is authorized for the session
    async fn is_tool_authorized(&self, tool_call: &ToolCall) -> Result<bool> {
        // Check against allowlist
        let response = self.http_client
            .post(&format!("{}/api/check-authorization", self.config.broker_endpoint))
            .json(tool_call)
            .send()
            .await
            .context("Failed to check tool authorization")?;

        if response.status().is_success() {
            let result: serde_json::Value = response.json().await
                .context("Failed to parse authorization response")?;
            Ok(result.get("authorized").and_then(|v| v.as_bool()).unwrap_or(false))
        } else {
            warn!("Authorization check failed: {}", response.status());
            Ok(false)
        }
    }

    /// Detect cross-tenant access attempts
    async fn detect_cross_tenant_access(&self, tool_call: &ToolCall) -> Result<bool> {
        // Check if the tool call attempts to access resources from other tenants
        for (key, value) in &tool_call.parameters {
            if let Some(value_str) = value.as_str() {
                // Check for tenant ID patterns in parameters
                if value_str.contains("tenant_id") || value_str.contains("cross_tenant") {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }

    /// Detect privacy violations
    async fn detect_privacy_violation(&self, tool_call: &ToolCall) -> Result<bool> {
        // Check for PII or sensitive data in parameters
        let sensitive_patterns = [
            "password", "secret", "key", "token", "ssn", "credit_card",
            "email", "phone", "address", "dob", "social_security"
        ];

        for (key, value) in &tool_call.parameters {
            let key_lower = key.to_lowercase();
            for pattern in &sensitive_patterns {
                if key_lower.contains(pattern) {
                    return Ok(true);
                }
            }

            if let Some(value_str) = value.as_str() {
                let value_lower = value_str.to_lowercase();
                for pattern in &sensitive_patterns {
                    if value_lower.contains(pattern) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }

    /// Create an approval request for high-risk operations
    async fn create_approval_request(&self, tool_call: ToolCall) -> Result<ValidationResult> {
        let request_id = Uuid::new_v4().to_string();
        let expires_at = chrono::Utc::now() + chrono::Duration::minutes(self.config.approval_timeout_minutes as i64);

        let approval_request = ApprovalRequest {
            request_id: request_id.clone(),
            session_id: tool_call.session_id.clone(),
            tool_call: tool_call.clone(),
            risk_score: tool_call.risk_score,
            reason: format!("Risk score {} exceeds threshold {}", 
                          tool_call.risk_score, self.config.risk_threshold),
            created_at: chrono::Utc::now().to_rfc3339(),
            expires_at: expires_at.to_rfc3339(),
            status: ApprovalStatus::Pending,
        };

        // Store the approval request
        {
            let mut approvals = self.pending_approvals.write().await;
            approvals.insert(request_id.clone(), approval_request);
        }

        // Send to broker for human approval
        let response = self.http_client
            .post(&format!("{}/api/approval-requests", self.config.broker_endpoint))
            .json(&approval_request)
            .send()
            .await
            .context("Failed to create approval request")?;

        if response.status().is_success() {
            info!("Created approval request: {}", request_id);
            Ok(ValidationResult::PendingApproval(request_id))
        } else {
            error!("Failed to create approval request: {}", response.status());
            Ok(ValidationResult::Denied("Failed to create approval request".to_string()))
        }
    }

    /// Record a violation
    async fn record_violation(&self, violation: Violation) {
        let mut violations = self.violations.write().await;
        violations.push(violation.clone());

        // Send violation to broker
        if let Err(e) = self.http_client
            .post(&format!("{}/api/violations", self.config.broker_endpoint))
            .json(&violation)
            .send()
            .await {
            error!("Failed to send violation to broker: {}", e);
        }

        error!("VIOLATION: {:?}", violation);
    }

    /// Check approval status
    pub async fn check_approval_status(&self, request_id: &str) -> Result<Option<ApprovalStatus>> {
        let approvals = self.pending_approvals.read().await;
        if let Some(request) = approvals.get(request_id) {
            // Check if expired
            if let Ok(expires_at) = chrono::DateTime::parse_from_rfc3339(&request.expires_at) {
                if chrono::Utc::now() > expires_at {
                    return Ok(Some(ApprovalStatus::Expired));
                }
            }
            Ok(Some(request.status.clone()))
        } else {
            Ok(None)
        }
    }

    /// Get all violations
    pub async fn get_violations(&self) -> Vec<Violation> {
        let violations = self.violations.read().await;
        violations.clone()
    }

    /// Get pending approvals
    pub async fn get_pending_approvals(&self) -> Vec<ApprovalRequest> {
        let approvals = self.pending_approvals.read().await;
        approvals.values().cloned().collect()
    }
}

/// Result of tool call validation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationResult {
    Allowed,
    Denied(String),
    PendingApproval(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_deny_by_default() {
        let config = EnforcementConfig {
            deny_by_default: true,
            ..Default::default()
        };
        let engine = EnforcementEngine::new(config).unwrap();

        let tool_call = ToolCall {
            call_id: "test-1".to_string(),
            session_id: "session-1".to_string(),
            tool_name: "test_tool".to_string(),
            parameters: HashMap::new(),
            risk_score: 0.1,
            kernel_decision: None,
            timestamp: chrono::Utc::now().to_rfc3339(),
        };

        let result = engine.validate_tool_call(tool_call).await.unwrap();
        assert!(matches!(result, ValidationResult::Denied(_)));
    }

    #[tokio::test]
    async fn test_risk_threshold() {
        let config = EnforcementConfig {
            risk_threshold: 0.5,
            enable_human_approval: false,
            ..Default::default()
        };
        let engine = EnforcementEngine::new(config).unwrap();

        let tool_call = ToolCall {
            call_id: "test-2".to_string(),
            session_id: "session-2".to_string(),
            tool_name: "test_tool".to_string(),
            parameters: HashMap::new(),
            risk_score: 0.8,
            kernel_decision: None,
            timestamp: chrono::Utc::now().to_rfc3339(),
        };

        let result = engine.validate_tool_call(tool_call).await.unwrap();
        assert!(matches!(result, ValidationResult::Denied(_)));
    }
} 