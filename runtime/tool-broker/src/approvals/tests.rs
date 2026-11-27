// SPDX-License-Identifier: Apache-2.0
use super::*;
use std::sync::Arc;

fn call(risk: f64) -> ToolCall {
    ToolCall {
        call_id: "call-1".into(), session_id: "tenant-a:plan-1".into(),
        tool_name: "search".into(), parameters: HashMap::new(), risk_score: risk,
        kernel_decision: None, timestamp: "2023-11-14T22:13:20Z".into(),
    }
}

fn approver(id: &str) -> Approver {
    Approver {
        approver_id: id.into(), name: id.into(), email: String::new(),
        role: ApproverRole::SecurityAdmin,
        permissions: vec![ApprovalPermission::CriticalRisk,
            ApprovalPermission::SpecificTools(vec!["search".into()]),
            ApprovalPermission::SpecificTenants(vec!["tenant-a".into()])],
        created_at: "2023-11-14T22:13:20Z".into(),
    }
}

async fn create(manager: &ApprovalManager, risk: f64) -> String {
    manager.create_approval_request(call(risk), risk, "fixture".into()).await.unwrap()
}

#[tokio::test]
async fn create_and_auto_approval() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    let id = create(&manager, 0.1).await;
    assert_eq!(manager.get_approval_status(&id).await.unwrap(), Some(ApprovalStatus::Pending));
    let manager = ApprovalManager::new(ApprovalConfig { auto_approve_low_risk: true, ..Default::default() });
    let id = create(&manager, 0.1).await;
    assert_eq!(manager.get_approval_status(&id).await.unwrap(), Some(ApprovalStatus::Approved));
    assert_eq!(manager.get_approval_history(None).await.len(), 1);
    let id = create(&manager, 0.3).await;
    assert_eq!(manager.get_approval_status(&id).await.unwrap(), Some(ApprovalStatus::Pending));
}

#[tokio::test]
async fn invalid_risk_and_configuration_rejected() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    for risk in [f64::NAN, f64::INFINITY, -0.01, 1.01] {
        assert!(manager.create_approval_request(call(risk), risk, "bad".into()).await.is_err());
    }
    assert!(manager.create_approval_request(call(0.8), 0.1, "mismatch".into()).await.is_err());
    assert!(manager.get_pending_requests().await.is_empty());
    for config in [
        ApprovalConfig { default_timeout_minutes: 0, ..Default::default() },
        ApprovalConfig { max_approvers_per_request: 1, ..Default::default() },
    ] {
        let manager = ApprovalManager::new(config);
        assert!(manager.create_approval_request(call(0.8), 0.8, "bad".into()).await.is_err());
    }
}

#[tokio::test]
async fn quorum_requires_distinct_currently_authorized_approvers() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    for id in ["a", "b"] { manager.add_approver(approver(id)).await.unwrap(); }
    let id = create(&manager, 0.7).await;
    assert!(!manager.approve_request(&id, "a", None).await.unwrap());
    assert!(!manager.approve_request(&id, "a", None).await.unwrap());
    assert!(!manager.approve_request(&id, "unknown", None).await.unwrap());
    assert_eq!(manager.get_pending_requests().await[0].approval_votes.len(), 1);
    manager.remove_approver("a").await.unwrap();
    assert!(!manager.approve_request(&id, "b", None).await.unwrap());
    manager.add_approver(approver("a")).await.unwrap();
    assert!(manager.approve_request(&id, "a", None).await.unwrap());
    assert!(!manager.approve_request(&id, "b", None).await.unwrap());
    assert!(!manager.deny_request(&id, "b", None).await.unwrap());
    let history = manager.get_approval_history(None).await;
    assert_eq!(history.len(), 1);
    assert_eq!(history[0].approval_votes.len(), 2);
    assert_eq!(history[0].status, ApprovalStatus::Approved);
}

#[tokio::test]
async fn replacing_approver_invalidates_pending_vote() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    manager.add_approver(approver("a")).await.unwrap();
    manager.add_approver(approver("b")).await.unwrap();
    let id = create(&manager, 0.9).await;
    assert!(!manager.approve_request(&id, "a", None).await.unwrap());
    manager.add_approver(approver("a")).await.unwrap();
    assert!(!manager.approve_request(&id, "b", None).await.unwrap());
    assert!(manager.approve_request(&id, "a", None).await.unwrap());
}

#[tokio::test]
async fn tenant_tool_and_risk_permissions_are_required() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    for (id, permissions) in [
        ("wrong-tenant", vec![ApprovalPermission::CriticalRisk, ApprovalPermission::AllTools, ApprovalPermission::SpecificTenants(vec!["tenant-b".into()])]),
        ("wrong-tool", vec![ApprovalPermission::CriticalRisk, ApprovalPermission::AllTenants, ApprovalPermission::SpecificTools(vec!["email".into()])]),
        ("wrong-risk", vec![ApprovalPermission::LowRisk, ApprovalPermission::AllTools, ApprovalPermission::AllTenants]),
    ] {
        let mut a = approver(id);
        a.permissions = permissions;
        manager.add_approver(a).await.unwrap();
    }
    assert!(manager.add_approver(approver("system")).await.is_err());
    let id = create(&manager, 0.5).await;
    for who in ["wrong-tenant", "wrong-tool", "wrong-risk", "system"] {
        assert!(!manager.approve_request(&id, who, None).await.unwrap());
        assert!(!manager.deny_request(&id, who, None).await.unwrap());
    }
    assert_eq!(manager.get_pending_requests().await[0].approval_votes.len(), 0);
}

#[tokio::test]
async fn malformed_and_expired_records_fail_closed_and_terminal_history_survives() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    manager.add_approver(approver("a")).await.unwrap();
    let malformed = create(&manager, 0.5).await;
    let stale = create(&manager, 0.5).await;
    let approved = create(&manager, 0.5).await;
    let denied = create(&manager, 0.5).await;
    assert!(manager.approve_request(&approved, "a", None).await.unwrap());
    assert!(manager.deny_request(&denied, "a", None).await.unwrap());
    {
        let mut state = manager.state.write().await;
        state.requests.get_mut(&malformed).unwrap().expires_at = "invalid".into();
        for id in [&stale, &approved, &denied] {
            state.requests.get_mut(id).unwrap().expires_at = "2000-01-01T00:00:00Z".into();
        }
    }
    assert!(!manager.approve_request(&malformed, "a", None).await.unwrap());
    assert!(!manager.deny_request(&stale, "a", None).await.unwrap());
    assert_eq!(manager.cleanup_expired_requests().await.unwrap(), 0);
    for id in [&malformed, &stale] {
        assert_eq!(manager.get_approval_status(id).await.unwrap(), Some(ApprovalStatus::Expired));
    }
    assert_eq!(manager.get_approval_status(&approved).await.unwrap(), Some(ApprovalStatus::Approved));
    assert_eq!(manager.get_approval_status(&denied).await.unwrap(), Some(ApprovalStatus::Denied));
    assert!(manager.get_pending_requests().await.is_empty());
    assert_eq!(manager.get_approval_history(None).await.len(), 4);
}

#[tokio::test]
async fn exact_deadline_and_backward_clock_boundary() {
    let manager = ApprovalManager::new(ApprovalConfig::default());
    let id = create(&manager, 0.5).await;
    let mut state = manager.state.write().await;
    let request = state.requests.get_mut(&id).unwrap();
    request.created_at = "2023-11-14T22:13:20Z".into();
    request.expires_at = "2023-11-14T22:13:21Z".into();
    for (seconds, nanos, expected) in [
        (1_699_999_999, 999_999_999, false),
        (1_700_000_000, 0, true),
        (1_700_000_000, 999_999_999, true),
        (1_700_000_001, 0, false),
    ] {
        assert_eq!(fresh(request, UtcTimestamp::from_timestamp(seconds, nanos).unwrap()), expected);
    }
    observe(request, UtcTimestamp::from_timestamp(1_700_000_001, 0).unwrap());
    observe(request, UtcTimestamp::from_timestamp(1_700_000_000, 0).unwrap());
    assert_eq!(request.status, ApprovalStatus::Expired);
}

#[tokio::test]
async fn concurrent_votes_produce_exactly_one_terminal_transition() {
    let manager = Arc::new(ApprovalManager::new(ApprovalConfig::default()));
    for who in ["a", "b"] { manager.add_approver(approver(who)).await.unwrap(); }
    let id = create(&manager, 0.9).await;
    let mut tasks = tokio::task::JoinSet::new();
    for i in 0..16 {
        let manager = manager.clone();
        let id = id.clone();
        tasks.spawn(async move { manager.approve_request(&id, if i % 2 == 0 { "a" } else { "b" }, None).await.unwrap() });
    }
    let mut completed = 0;
    while let Some(result) = tasks.join_next().await {
        if result.unwrap() { completed += 1; }
    }
    assert_eq!(completed, 1);
    let history = manager.get_approval_history(None).await;
    assert_eq!(history.len(), 1);
    assert_eq!(history[0].approval_votes.len(), 2);
}

fn code(status: ApprovalStatus) -> u8 {
    match status {
        ApprovalStatus::Pending => 0, ApprovalStatus::Approved => 1,
        ApprovalStatus::Denied => 2, ApprovalStatus::Expired => 3, ApprovalStatus::Cancelled => 4,
    }
}

#[test]
#[ignore = "requires generated Lean transition table"]
fn lean_transition_correspondence() {
    let path = std::env::var("PF_APPROVAL_LEAN_TABLE").expect("Lean table path");
    let expected = std::fs::read_to_string(path).unwrap();
    let mut actual = String::new();
    let statuses = [ApprovalStatus::Pending, ApprovalStatus::Approved, ApprovalStatus::Denied,
                    ApprovalStatus::Expired, ApprovalStatus::Cancelled];
    for status in statuses {
        for fresh in [false, true] {
            for authorized in [false, true] {
                for quorum in [false, true] {
                    for (event_code, event) in [Event::Approve, Event::Deny, Event::Observe].into_iter().enumerate() {
                        actual.push_str(&format!("{}\t{}\t{}\t{}\t{}\t{}\n",
                            code(status), u8::from(fresh), u8::from(authorized), u8::from(quorum),
                            event_code, code(transition(status, fresh, authorized, quorum, event))));
                    }
                }
            }
        }
    }
    assert_eq!(actual.lines().count(), 120);
    assert_eq!(actual, expected);
}
