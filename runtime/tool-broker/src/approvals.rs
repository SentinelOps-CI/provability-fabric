// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{anyhow, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::RwLock;
use tracing::{info, warn};
use uuid::Uuid;
use crate::utc_timestamp::UtcTimestamp;

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
    #[serde(default)]
    pub approval_votes: Vec<ApprovalVote>,
}

/// Recorded vote from an approver identity already checked by the caller.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApprovalVote {
    pub approver_id: String,
    pub notes: Option<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
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

/// Inputs to the finite transition relation. Authorization and quorum are
/// computed under the same lock as the request and approver registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event { Approve, Deny, Observe }

fn transition(status: ApprovalStatus, fresh: bool, authorized: bool, quorum: bool, event: Event) -> ApprovalStatus {
    use ApprovalStatus::*;
    if status != Pending { return status; }
    if !fresh { return Expired; }
    if !authorized { return Pending; }
    match event {
        Event::Approve if quorum => Approved,
        Event::Deny => Denied,
        _ => Pending,
    }
}

fn valid_risk(risk: f64) -> bool {
    risk.is_finite() && (0.0..=1.0).contains(&risk)
}

fn fresh(request: &ApprovalRequest, now: UtcTimestamp) -> bool {
    match (UtcTimestamp::parse(&request.created_at), UtcTimestamp::parse(&request.expires_at)) {
        (Some(created), Some(expires)) => created <= now && now < expires,
        _ => false,
    }
}

fn observe(request: &mut ApprovalRequest, now: UtcTimestamp) {
    request.status = transition(request.status, fresh(request, now), false, false, Event::Observe);
}

fn permitted(approver: &Approver, request: &ApprovalRequest) -> bool {
    if approver.approver_id.is_empty() || approver.approver_id == "system" ||
       !valid_risk(request.risk_score) || request.risk_score != request.tool_call.risk_score {
        return false;
    }
    let risk = match request.risk_score {
        r if r < 0.3 => ApprovalPermission::LowRisk,
        r if r < 0.7 => ApprovalPermission::MediumRisk,
        r if r < 0.9 => ApprovalPermission::HighRisk,
        _ => ApprovalPermission::CriticalRisk,
    };
    let permissions = &approver.permissions;
    let tenant = request.session_id.split(':').next().unwrap_or("");
    !tenant.is_empty() &&
    (permissions.contains(&risk) || permissions.contains(&ApprovalPermission::CriticalRisk)) &&
    permissions.iter().any(|p| matches!(p, ApprovalPermission::AllTools) ||
        matches!(p, ApprovalPermission::SpecificTools(tools) if tools.contains(&request.tool_call.tool_name))) &&
    permissions.iter().any(|p| matches!(p, ApprovalPermission::AllTenants) ||
        matches!(p, ApprovalPermission::SpecificTenants(tenants) if tenants.iter().any(|t| t == tenant)))
}

#[derive(Default)]
struct ApprovalState {
    requests: HashMap<String, ApprovalRequest>,
    approvers: HashMap<String, Approver>,
}

/// Process-local approval bookkeeping. Terminal decisions are immutable.
/// The caller is responsible for authenticating approver identities; this
/// manager does not issue execution permits or provide persistent audit storage.
pub struct ApprovalManager {
    config: ApprovalConfig,
    state: RwLock<ApprovalState>,
}

impl ApprovalManager {
    pub fn new(config: ApprovalConfig) -> Self {
        Self { config, state: RwLock::new(ApprovalState::default()) }
    }

    fn required_votes(&self, risk: f64) -> usize {
        if self.config.require_multiple_approvers_for_high_risk && risk >= 0.7 { 2 } else { 1 }
    }

    pub async fn create_approval_request(&self, tool_call: ToolCall, risk_score: f64, reason: String) -> Result<String> {
        if !valid_risk(risk_score) || risk_score != tool_call.risk_score {
            return Err(anyhow!("Invalid or inconsistent approval risk"));
        }
        if tool_call.session_id.split(':').next().unwrap_or("").is_empty() ||
           tool_call.tool_name.is_empty() || tool_call.call_id.is_empty() {
            return Err(anyhow!("Missing approval request identity"));
        }
        if self.config.default_timeout_minutes == 0 ||
           (self.config.max_approvers_per_request as usize) < self.required_votes(risk_score) {
            return Err(anyhow!("Invalid approval timeout or quorum configuration"));
        }
        let mut state = self.state.write().await;
        let now = UtcTimestamp::now();
        let expires = now.checked_add_minutes(self.config.default_timeout_minutes)
            .ok_or_else(|| anyhow!("Approval deadline outside supported domain"))?;
        let request_id = Uuid::new_v4().to_string();
        if state.requests.contains_key(&request_id) {
            return Err(anyhow!("Duplicate approval request identifier"));
        }
        let mut request = ApprovalRequest {
            request_id: request_id.clone(),
            session_id: tool_call.session_id.clone(),
            tool_call,
            risk_score,
            reason,
            created_at: now.to_rfc3339()?,
            expires_at: expires.to_rfc3339()?,
            status: ApprovalStatus::Pending,
            approver_id: None,
            approval_notes: None,
            approval_votes: Vec::new(),
        };
        if self.config.auto_approve_low_risk && risk_score < 0.3 {
            request.status = transition(request.status, fresh(&request, now), true, true, Event::Approve);
            if request.status == ApprovalStatus::Approved {
                request.approver_id = Some("system".into());
                request.approval_notes = Some("Auto-approved for low risk".into());
            }
        }
        let pending = request.status == ApprovalStatus::Pending;
        state.requests.insert(request_id.clone(), request);
        drop(state);
        if pending && !self.config.notification_channels.is_empty() {
            // The existing repository has no notification transport. Do not
            // report a successful email, Slack message or webhook delivery.
            warn!("Approval request recorded; notification transport unavailable: {}", request_id);
        }
        info!("Created approval request: {}", request_id);
        Ok(request_id)
    }

    /// Returns true only when this call completes a new approval. A first
    /// vote below quorum is recorded, but returns false (still pending).
    pub async fn approve_request(&self, request_id: &str, approver_id: &str, notes: Option<String>) -> Result<bool> {
        let mut state = self.state.write().await;
        let ApprovalState { requests, approvers } = &mut *state;
        let Some(request) = requests.get_mut(request_id) else { return Ok(false); };
        let now = UtcTimestamp::now();
        observe(request, now);
        if request.status != ApprovalStatus::Pending { return Ok(false); }
        let authorized = approvers.get(approver_id).is_some_and(|a| permitted(a, request));
        if !authorized { return Ok(false); }
        // Re-evaluate prior votes against the current registry. The write
        // lock prevents revocation/configuration races during this decision.
        let mut votes = std::mem::take(&mut request.approval_votes);
        votes.retain(|v| approvers.get(&v.approver_id).is_some_and(|a| permitted(a, request)));
        request.approval_votes = votes;
        if request.approval_votes.iter().any(|v| v.approver_id == approver_id) ||
           request.approval_votes.len() >= self.config.max_approvers_per_request as usize {
            return Ok(false);
        }
        request.approval_votes.push(ApprovalVote { approver_id: approver_id.to_owned(), notes: notes.clone() });
        let quorum = request.approval_votes.len() >= self.required_votes(request.risk_score);
        request.status = transition(request.status, fresh(request, now), authorized, quorum, Event::Approve);
        if request.status == ApprovalStatus::Approved {
            request.approver_id = Some(approver_id.to_owned());
            request.approval_notes = notes;
            info!("Request {} approved", request_id);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub async fn deny_request(&self, request_id: &str, approver_id: &str, notes: Option<String>) -> Result<bool> {
        let mut state = self.state.write().await;
        let ApprovalState { requests, approvers } = &mut *state;
        let Some(request) = requests.get_mut(request_id) else { return Ok(false); };
        let now = UtcTimestamp::now();
        observe(request, now);
        if request.status != ApprovalStatus::Pending { return Ok(false); }
        let authorized = approvers.get(approver_id).is_some_and(|a| permitted(a, request));
        request.status = transition(request.status, fresh(request, now), authorized, false, Event::Deny);
        if request.status == ApprovalStatus::Denied {
            request.approver_id = Some(approver_id.to_owned());
            request.approval_notes = notes;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    pub async fn get_approval_status(&self, request_id: &str) -> Result<Option<ApprovalStatus>> {
        let mut state = self.state.write().await;
        let now = UtcTimestamp::now();
        Ok(state.requests.get_mut(request_id).map(|request| {
            observe(request, now);
            request.status
        }))
    }

    pub async fn get_pending_requests(&self) -> Vec<ApprovalRequest> {
        let mut state = self.state.write().await;
        let now = UtcTimestamp::now();
        for request in state.requests.values_mut() { observe(request, now); }
        state.requests.values().filter(|r| r.status == ApprovalStatus::Pending).cloned().collect()
    }

    /// Historical decisions are not evidence of a currently valid execution permit.
    pub async fn get_approval_history(&self, limit: Option<usize>) -> Vec<ApprovalRequest> {
        let mut state = self.state.write().await;
        let now = UtcTimestamp::now();
        for request in state.requests.values_mut() { observe(request, now); }
        let mut history: Vec<_> = state.requests.values().filter(|r| r.status != ApprovalStatus::Pending).cloned().collect();
        history.sort_by(|a, b| UtcTimestamp::parse(&b.created_at).cmp(&UtcTimestamp::parse(&a.created_at))
            .then_with(|| a.request_id.cmp(&b.request_id)));
        if let Some(limit) = limit { history.truncate(limit); }
        history
    }

    pub async fn add_approver(&self, approver: Approver) -> Result<()> {
        if approver.approver_id.is_empty() || approver.approver_id == "system" {
            return Err(anyhow!("Invalid or reserved approver identifier"));
        }
        let mut state = self.state.write().await;
        let id = approver.approver_id.clone();
        // Replacing a registry entry invalidates its pending votes, even
        // if the replacement happens to have the same permissions.
        for request in state.requests.values_mut().filter(|r| r.status == ApprovalStatus::Pending) {
            request.approval_votes.retain(|v| v.approver_id != id);
        }
        state.approvers.insert(id, approver);
        Ok(())
    }

    pub async fn remove_approver(&self, approver_id: &str) -> Result<()> {
        let mut state = self.state.write().await;
        state.approvers.remove(approver_id);
        for request in state.requests.values_mut().filter(|r| r.status == ApprovalStatus::Pending) {
            request.approval_votes.retain(|v| v.approver_id != approver_id);
        }
        Ok(())
    }

    pub async fn get_approvers(&self) -> Vec<Approver> {
        self.state.read().await.approvers.values().cloned().collect()
    }

    /// Mark newly expired requests; never remove or rewrite a terminal decision.
    pub async fn cleanup_expired_requests(&self) -> Result<usize> {
        let mut state = self.state.write().await;
        let now = UtcTimestamp::now();
        let mut count = 0;
        for request in state.requests.values_mut() {
            let prior = request.status;
            observe(request, now);
            if prior == ApprovalStatus::Pending && request.status == ApprovalStatus::Expired {
                count += 1;
            }
        }
        Ok(count)
    }
}

#[cfg(test)]
mod tests;
