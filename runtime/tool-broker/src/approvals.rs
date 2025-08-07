// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::RwLock;
use tracing::{error, info, warn};
use uuid::Uuid;
use chrono::{DateTime, Utc};
use std::sync::Arc;

/// Represents a human approval request
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
    pub approver_id: Option<String>,
    pub approval_notes: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ApprovalStatus {
    Pending,
    Approved,
    Denied,
    Expired,
    Cancelled,
}

/// Represents a tool call that requires approval
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

/// Represents a kernel decision
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

/// Represents an approver
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Approver {
    pub approver_id: String,
    pub name: String,
    pub email: String,
    pub role: ApproverRole,
    pub permissions: Vec<ApprovalPermission>,
    pub created_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ApproverRole {
    SecurityAdmin,
    SystemAdmin,
    RiskManager,
    ComplianceOfficer,
    TeamLead,
    Developer,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ApprovalPermission {
    LowRisk,      // Risk score < 0.3
    MediumRisk,   // Risk score < 0.7
    HighRisk,     // Risk score < 0.9
    CriticalRisk, // Any risk score
    AllTools,
    SpecificTools(Vec<String>),
    AllTenants,
    SpecificTenants(Vec<String>),
}

/// Configuration for approval workflows
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApprovalConfig {
    pub default_timeout_minutes: u32,
    pub escalation_timeout_minutes: u32,
    pub max_approvers_per_request: u32,
    pub require_multiple_approvers_for_high_risk: bool,
    pub auto_approve_low_risk: bool,
    pub notification_channels: Vec<String>,
}

impl Default for ApprovalConfig {
    fn default() -> Self {
        Self {
            default_timeout_minutes: 30,
            escalation_timeout_minutes: 60,
            max_approvers_per_request: 3,
            require_multiple_approvers_for_high_risk: true,
            auto_approve_low_risk: false,
            notification_channels: vec!["email".to_string(), "slack".to_string()],
        }
    }
}

/// Main approval manager
pub struct ApprovalManager {
    config: ApprovalConfig,
    pending_requests: Arc<RwLock<HashMap<String, ApprovalRequest>>>,
    approvers: Arc<RwLock<HashMap<String, Approver>>>,
    approval_history: Arc<RwLock<Vec<ApprovalRequest>>>,
}

impl ApprovalManager {
    pub fn new(config: ApprovalConfig) -> Self {
        Self {
            config,
            pending_requests: Arc::new(RwLock::new(HashMap::new())),
            approvers: Arc::new(RwLock::new(HashMap::new())),
            approval_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// Create a new approval request
    pub async fn create_approval_request(&self, tool_call: ToolCall, risk_score: f64, reason: String) -> Result<String> {
        let request_id = Uuid::new_v4().to_string();
        let expires_at = Utc::now() + chrono::Duration::minutes(self.config.default_timeout_minutes as i64);

        let approval_request = ApprovalRequest {
            request_id: request_id.clone(),
            session_id: tool_call.session_id.clone(),
            tool_call,
            risk_score,
            reason,
            created_at: Utc::now().to_rfc3339(),
            expires_at: expires_at.to_rfc3339(),
            status: ApprovalStatus::Pending,
            approver_id: None,
            approval_notes: None,
        };

        // Store the request
        {
            let mut requests = self.pending_requests.write().await;
            requests.insert(request_id.clone(), approval_request);
        }

        // Auto-approve low risk requests if configured
        if self.config.auto_approve_low_risk && risk_score < 0.3 {
            self.auto_approve_request(&request_id).await?;
        } else {
            // Send notifications
            self.send_approval_notifications(&approval_request).await?;
        }

        info!("Created approval request: {}", request_id);
        Ok(request_id)
    }

    /// Approve a request
    pub async fn approve_request(&self, request_id: &str, approver_id: &str, notes: Option<String>) -> Result<bool> {
        let mut requests = self.pending_requests.write().await;
        
        if let Some(request) = requests.get_mut(request_id) {
            // Check if approver has permission
            if !self.can_approver_approve(approver_id, request).await? {
                return Ok(false);
            }

            // Check if request is still pending
            if request.status != ApprovalStatus::Pending {
                warn!("Request {} is not pending (status: {:?})", request_id, request.status);
                return Ok(false);
            }

            // Check if request has expired
            if let Ok(expires_at) = DateTime::parse_from_rfc3339(&request.expires_at) {
                if Utc::now() > expires_at {
                    request.status = ApprovalStatus::Expired;
                    return Ok(false);
                }
            }

            // Update request
            request.status = ApprovalStatus::Approved;
            request.approver_id = Some(approver_id.to_string());
            request.approval_notes = notes;

            // Move to history
            let request_clone = request.clone();
            drop(requests);
            
            {
                let mut history = self.approval_history.write().await;
                history.push(request_clone);
            }

            info!("Request {} approved by {}", request_id, approver_id);
            Ok(true)
        } else {
            warn!("Request {} not found", request_id);
            Ok(false)
        }
    }

    /// Deny a request
    pub async fn deny_request(&self, request_id: &str, approver_id: &str, notes: Option<String>) -> Result<bool> {
        let mut requests = self.pending_requests.write().await;
        
        if let Some(request) = requests.get_mut(request_id) {
            // Check if approver has permission
            if !self.can_approver_approve(approver_id, request).await? {
                return Ok(false);
            }

            // Check if request is still pending
            if request.status != ApprovalStatus::Pending {
                warn!("Request {} is not pending (status: {:?})", request_id, request.status);
                return Ok(false);
            }

            // Update request
            request.status = ApprovalStatus::Denied;
            request.approver_id = Some(approver_id.to_string());
            request.approval_notes = notes;

            // Move to history
            let request_clone = request.clone();
            drop(requests);
            
            {
                let mut history = self.approval_history.write().await;
                history.push(request_clone);
            }

            info!("Request {} denied by {}", request_id, approver_id);
            Ok(true)
        } else {
            warn!("Request {} not found", request_id);
            Ok(false)
        }
    }

    /// Check if an approver can approve a specific request
    async fn can_approver_approve(&self, approver_id: &str, request: &ApprovalRequest) -> Result<bool> {
        let approvers = self.approvers.read().await;
        
        if let Some(approver) = approvers.get(approver_id) {
            // Check risk level permissions
            let risk_permission = match request.risk_score {
                r if r < 0.3 => ApprovalPermission::LowRisk,
                r if r < 0.7 => ApprovalPermission::MediumRisk,
                r if r < 0.9 => ApprovalPermission::HighRisk,
                _ => ApprovalPermission::CriticalRisk,
            };

            if !approver.permissions.contains(&risk_permission) && 
               !approver.permissions.contains(&ApprovalPermission::CriticalRisk) {
                return Ok(false);
            }

            // Check tool permissions
            let tool_name = &request.tool_call.tool_name;
            let has_tool_permission = approver.permissions.iter().any(|p| {
                matches!(p, ApprovalPermission::AllTools) ||
                matches!(p, ApprovalPermission::SpecificTools(tools) if tools.contains(tool_name))
            });

            if !has_tool_permission {
                return Ok(false);
            }

            // Check tenant permissions
            let tenant_id = &request.session_id.split(':').next().unwrap_or("default");
            let has_tenant_permission = approver.permissions.iter().any(|p| {
                matches!(p, ApprovalPermission::AllTenants) ||
                matches!(p, ApprovalPermission::SpecificTenants(tenants) if tenants.contains(&tenant_id.to_string()))
            });

            if !has_tenant_permission {
                return Ok(false);
            }

            Ok(true)
        } else {
            warn!("Approver {} not found", approver_id);
            Ok(false)
        }
    }

    /// Auto-approve a request (for low-risk operations)
    async fn auto_approve_request(&self, request_id: &str) -> Result<bool> {
        let mut requests = self.pending_requests.write().await;
        
        if let Some(request) = requests.get_mut(request_id) {
            request.status = ApprovalStatus::Approved;
            request.approver_id = Some("system".to_string());
            request.approval_notes = Some("Auto-approved for low risk".to_string());

            // Move to history
            let request_clone = request.clone();
            drop(requests);
            
            {
                let mut history = self.approval_history.write().await;
                history.push(request_clone);
            }

            info!("Request {} auto-approved", request_id);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Send approval notifications
    async fn send_approval_notifications(&self, request: &ApprovalRequest) -> Result<()> {
        for channel in &self.config.notification_channels {
            match channel.as_str() {
                "email" => self.send_email_notification(request).await?,
                "slack" => self.send_slack_notification(request).await?,
                "webhook" => self.send_webhook_notification(request).await?,
                _ => warn!("Unknown notification channel: {}", channel),
            }
        }
        Ok(())
    }

    /// Send email notification
    async fn send_email_notification(&self, request: &ApprovalRequest) -> Result<()> {
        // Implementation would integrate with email service
        info!("Email notification sent for request: {}", request.request_id);
        Ok(())
    }

    /// Send Slack notification
    async fn send_slack_notification(&self, request: &ApprovalRequest) -> Result<()> {
        // Implementation would integrate with Slack API
        info!("Slack notification sent for request: {}", request.request_id);
        Ok(())
    }

    /// Send webhook notification
    async fn send_webhook_notification(&self, request: &ApprovalRequest) -> Result<()> {
        // Implementation would send HTTP POST to configured webhook
        info!("Webhook notification sent for request: {}", request.request_id);
        Ok(())
    }

    /// Get approval status
    pub async fn get_approval_status(&self, request_id: &str) -> Result<Option<ApprovalStatus>> {
        let requests = self.pending_requests.read().await;
        
        if let Some(request) = requests.get(request_id) {
            // Check if expired
            if let Ok(expires_at) = DateTime::parse_from_rfc3339(&request.expires_at) {
                if Utc::now() > expires_at {
                    return Ok(Some(ApprovalStatus::Expired));
                }
            }
            Ok(Some(request.status.clone()))
        } else {
            Ok(None)
        }
    }

    /// Get pending requests
    pub async fn get_pending_requests(&self) -> Vec<ApprovalRequest> {
        let requests = self.pending_requests.read().await;
        requests.values().cloned().collect()
    }

    /// Get approval history
    pub async fn get_approval_history(&self, limit: Option<usize>) -> Vec<ApprovalRequest> {
        let history = self.approval_history.read().await;
        let mut history_vec = history.clone();
        history_vec.sort_by(|a, b| b.created_at.cmp(&a.created_at));
        
        if let Some(limit) = limit {
            history_vec.truncate(limit);
        }
        
        history_vec
    }

    /// Add an approver
    pub async fn add_approver(&self, approver: Approver) -> Result<()> {
        let mut approvers = self.approvers.write().await;
        approvers.insert(approver.approver_id.clone(), approver);
        Ok(())
    }

    /// Remove an approver
    pub async fn remove_approver(&self, approver_id: &str) -> Result<()> {
        let mut approvers = self.approvers.write().await;
        approvers.remove(approver_id);
        Ok(())
    }

    /// Get all approvers
    pub async fn get_approvers(&self) -> Vec<Approver> {
        let approvers = self.approvers.read().await;
        approvers.values().cloned().collect()
    }

    /// Clean up expired requests
    pub async fn cleanup_expired_requests(&self) -> Result<usize> {
        let mut requests = self.pending_requests.write().await;
        let mut expired_count = 0;
        let mut expired_requests = Vec::new();

        for (request_id, request) in requests.iter() {
            if let Ok(expires_at) = DateTime::parse_from_rfc3339(&request.expires_at) {
                if Utc::now() > expires_at {
                    expired_requests.push(request_id.clone());
                    expired_count += 1;
                }
            }
        }

        for request_id in expired_requests {
            if let Some(mut request) = requests.remove(&request_id) {
                request.status = ApprovalStatus::Expired;
                let mut history = self.approval_history.write().await;
                history.push(request);
            }
        }

        if expired_count > 0 {
            info!("Cleaned up {} expired requests", expired_count);
        }

        Ok(expired_count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_create_approval_request() {
        let config = ApprovalConfig::default();
        let manager = ApprovalManager::new(config);

        let tool_call = ToolCall {
            call_id: "test-1".to_string(),
            session_id: "session-1".to_string(),
            tool_name: "test_tool".to_string(),
            parameters: HashMap::new(),
            risk_score: 0.5,
            kernel_decision: None,
            timestamp: Utc::now().to_rfc3339(),
        };

        let request_id = manager.create_approval_request(
            tool_call,
            0.5,
            "Test reason".to_string()
        ).await.unwrap();

        let status = manager.get_approval_status(&request_id).await.unwrap();
        assert_eq!(status, Some(ApprovalStatus::Pending));
    }

    #[tokio::test]
    async fn test_auto_approve_low_risk() {
        let mut config = ApprovalConfig::default();
        config.auto_approve_low_risk = true;
        let manager = ApprovalManager::new(config);

        let tool_call = ToolCall {
            call_id: "test-2".to_string(),
            session_id: "session-2".to_string(),
            tool_name: "test_tool".to_string(),
            parameters: HashMap::new(),
            risk_score: 0.1,
            kernel_decision: None,
            timestamp: Utc::now().to_rfc3339(),
        };

        let request_id = manager.create_approval_request(
            tool_call,
            0.1,
            "Low risk test".to_string()
        ).await.unwrap();

        let status = manager.get_approval_status(&request_id).await.unwrap();
        assert_eq!(status, Some(ApprovalStatus::Approved));
    }
} 