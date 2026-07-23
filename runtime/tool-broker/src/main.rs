// Tool broker with rate limiting and approvals; some code paths and types are reserved for future use.
#![allow(dead_code, unused_variables)]

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn};
use metrics::{counter, histogram};
use uuid::Uuid;
use chrono::{DateTime, Utc};

mod ratelimit;
mod approvals;

#[cfg(test)]
mod ratelimit_test;
#[cfg(test)]
mod integration_test;

use ratelimit::{RateLimiter, RateLimitConfig, RateLimitDecision};
use approvals::ApprovalManager;

#[derive(Debug, Deserialize, Serialize)]
struct KernelDecision {
    approved_steps: Vec<ApprovedStep>,
    reason: String,
    valid: bool,
    errors: Option<Vec<String>>,
    warnings: Option<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct ApprovedStep {
    step_index: usize,
    tool: String,
    args: HashMap<String, serde_json::Value>,
    receipts: Option<Vec<AccessReceipt>>,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct AccessReceipt {
    receipt_id: String,
    tenant: String,
    subject_id: String,
    query_hash: String,
    index_shard: String,
    timestamp: i64,
    result_hash: String,
    sign_alg: String,
    sig: String,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct ToolCall {
    tool: String,
    args: HashMap<String, serde_json::Value>,
    step_index: Option<usize>,
}

#[derive(Debug, Serialize)]
struct ToolResult {
    success: bool,
    result: Option<serde_json::Value>,
    error: Option<String>,
    execution_id: String,
    timestamp: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize)]
struct Violation {
    violation_type: String,
    reason: String,
    tool_call: ToolCall,
    timestamp: DateTime<Utc>,
}

/// Optional per-call context (JWT / explicit tenant override).
#[derive(Debug, Clone, Default)]
pub struct ExecutionContext {
    pub tenant_id: Option<String>,
    pub jwt: Option<String>,
}

/// Plan-scoped metadata captured at submit time.
#[derive(Debug, Clone)]
struct PlanContext {
    tenant_id: Option<String>,
}

struct ToolBroker {
    kernel_url: String,
    http_client: reqwest::Client,
    approved_steps: Arc<RwLock<HashMap<String, Vec<ApprovedStep>>>>,
    plan_contexts: Arc<RwLock<HashMap<String, PlanContext>>>,
    violation_log: Arc<RwLock<Vec<Violation>>>,
    rate_limiter: RateLimiter,
    approval_manager: ApprovalManager,
}

impl ToolBroker {
    pub fn new(kernel_url: String) -> Self {
        let http_client = reqwest::Client::builder()
            .pool_max_idle_per_host(10)
            .pool_idle_timeout(Duration::from_secs(30))
            .http2_prior_knowledge()
            .timeout(Duration::from_secs(30))
            .connect_timeout(Duration::from_secs(10))
            .tcp_keepalive(Some(Duration::from_secs(30)))
            .build()
            .expect("Failed to create HTTP client");

        let rate_limiter = RateLimiter::new(RateLimitConfig::default());
        let approval_manager = ApprovalManager::new(approvals::ApprovalConfig::default());

        Self {
            kernel_url,
            http_client,
            approved_steps: Arc::new(RwLock::new(HashMap::new())),
            plan_contexts: Arc::new(RwLock::new(HashMap::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
            rate_limiter,
            approval_manager,
        }
    }

    /// True when missing tenant must deny.
    /// Fail-closed by default (unset); opt out only with `PF_ENFORCE_TENANT=0`/`false`.
    pub fn tenant_enforced() -> bool {
        match std::env::var("PF_ENFORCE_TENANT") {
            Ok(v) => {
                let v = v.trim();
                !(v == "0" || v.eq_ignore_ascii_case("false"))
            }
            Err(_) => true,
        }
    }

    /// Resolve tenant from plan-bound context → explicit context tenant_id → step receipts.
    ///
    /// Unverified JWT payloads are **not** trusted for tenant binding (spoofable).
    /// Callers that authenticate JWTs must pass `ExecutionContext.tenant_id` from a
    /// verified claim, or bind tenant at plan approval time.
    pub async fn resolve_tenant_id(
        &self,
        plan_id: &str,
        step: &ApprovedStep,
        ctx: Option<&ExecutionContext>,
    ) -> Result<String, String> {
        if let Some(contexts) = self.plan_contexts.read().await.get(plan_id) {
            if let Some(ref tenant) = contexts.tenant_id {
                if !tenant.is_empty() {
                    return Ok(tenant.clone());
                }
            }
        }

        if let Some(ctx) = ctx {
            if let Some(ref tenant) = ctx.tenant_id {
                if !tenant.is_empty() {
                    return Ok(tenant.clone());
                }
            }
            if ctx.jwt.is_some() {
                warn!(
                    "ignoring unverified JWT for tenant binding; pass verified tenant_id on ExecutionContext"
                );
            }
        }

        if let Some(ref receipts) = step.receipts {
            for receipt in receipts {
                let tenant = receipt.tenant.trim();
                if !tenant.is_empty() {
                    return Ok(tenant.to_string());
                }
            }
        }

        if Self::tenant_enforced() {
            Err("missing tenant_id in plan/context (enforced)".to_string())
        } else {
            warn!("tenant_id missing; using default_tenant (PF_ENFORCE_TENANT=0)");
            Ok("default_tenant".to_string())
        }
    }

    /// Risk score from tool allow-list / policy metadata on the rate-limit config.
    pub fn risk_score_for_tool(&self, tool_name: &str) -> f64 {
        self.rate_limiter.risk_score_for_tool(tool_name)
    }

    /// Apply throttle delay; returns elapsed sleep duration (for tests).
    pub async fn apply_throttle_delay(delay_ms: u64) -> Duration {
        let start = Instant::now();
        if delay_ms > 0 {
            tokio::time::sleep(Duration::from_millis(delay_ms)).await;
        }
        start.elapsed()
    }

    async fn submit_plan(&self, plan_json: &str) -> Result<KernelDecision> {
        let start_time = Instant::now();

        let response = self
            .http_client
            .post(format!("{}/approve", self.kernel_url))
            .header("Content-Type", "application/json")
            .body(plan_json.to_string())
            .send()
            .await
            .context("Failed to submit plan to kernel")?;

        let latency = start_time.elapsed();
        histogram!("http_request_duration_seconds", latency.as_secs_f64());

        let decision: KernelDecision = response
            .json()
            .await
            .context("Failed to parse kernel decision")?;

        if decision.valid {
            let plan_id = self.extract_plan_id(plan_json)?;
            let tenant_id = Self::extract_tenant_from_plan(plan_json);
            {
                let mut approved_steps = self.approved_steps.write().await;
                approved_steps.insert(plan_id.clone(), decision.approved_steps.clone());
            }
            {
                let mut contexts = self.plan_contexts.write().await;
                contexts.insert(plan_id, PlanContext { tenant_id });
            }
            info!("Plan approved with {} steps", decision.approved_steps.len());
            counter!("plans_approved_total", 1);
        } else {
            warn!("Plan rejected: {}", decision.reason);
            counter!("plans_rejected_total", 1);
        }

        Ok(decision)
    }

    /// Install an approved plan locally (tests / offline paths).
    pub async fn install_approved_plan(
        &self,
        plan_id: &str,
        tenant_id: Option<String>,
        steps: Vec<ApprovedStep>,
    ) {
        self.approved_steps
            .write()
            .await
            .insert(plan_id.to_string(), steps);
        self.plan_contexts.write().await.insert(
            plan_id.to_string(),
            PlanContext { tenant_id },
        );
    }

    fn extract_plan_id(&self, plan_json: &str) -> Result<String> {
        let plan: serde_json::Value =
            serde_json::from_str(plan_json).context("Failed to parse plan JSON")?;

        plan.get("plan_id")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
            .ok_or_else(|| anyhow::anyhow!("Plan ID not found"))
    }

    fn extract_tenant_from_plan(plan_json: &str) -> Option<String> {
        let plan: serde_json::Value = serde_json::from_str(plan_json).ok()?;
        plan.get("tenant")
            .or_else(|| plan.get("tenant_id"))
            .and_then(|v| v.as_str())
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
    }

    async fn execute_tool(&self, tool_call: &ToolCall, plan_id: &str) -> Result<ToolResult> {
        self.execute_tool_with_context(tool_call, plan_id, None)
            .await
    }

    async fn execute_tool_with_context(
        &self,
        tool_call: &ToolCall,
        plan_id: &str,
        ctx: Option<&ExecutionContext>,
    ) -> Result<ToolResult> {
        let start_time = Instant::now();
        let timestamp = Utc::now();

        let approved_steps = self.approved_steps.read().await;
        let plan_steps = approved_steps.get(plan_id);

        match plan_steps {
            Some(steps) => {
                let approved_step = steps.iter().find(|step| {
                    step.tool == tool_call.tool
                        && step.step_index == tool_call.step_index.unwrap_or(0)
                });

                match approved_step {
                    Some(step) => {
                        let step = step.clone();
                        drop(approved_steps);
                        let result = self
                            .execute_approved_tool(tool_call, &step, plan_id, ctx)
                            .await?;

                        let latency = start_time.elapsed();
                        histogram!("tool_execution_duration_seconds", latency.as_secs_f64());
                        counter!("tool_executions_total", 1);

                        Ok(result)
                    }
                    None => {
                        let violation = Violation {
                            violation_type: "UNAPPROVED_TOOL".to_string(),
                            reason: "Tool call not in approved plan".to_string(),
                            tool_call: tool_call.clone(),
                            timestamp,
                        };

                        let mut violation_log = self.violation_log.write().await;
                        violation_log.push(violation);

                        counter!("tool_violations_total", 1);

                        Err(anyhow::anyhow!("Tool call not approved"))
                    }
                }
            }
            None => {
                let violation = Violation {
                    violation_type: "NO_APPROVED_PLAN".to_string(),
                    reason: "No approved plan found for plan ID".to_string(),
                    tool_call: tool_call.clone(),
                    timestamp,
                };

                let mut violation_log = self.violation_log.write().await;
                violation_log.push(violation);

                counter!("tool_violations_total", 1);

                Err(anyhow::anyhow!("No approved plan found"))
            }
        }
    }

    async fn execute_approved_tool(
        &self,
        tool_call: &ToolCall,
        step: &ApprovedStep,
        plan_id: &str,
        ctx: Option<&ExecutionContext>,
    ) -> Result<ToolResult> {
        let execution_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();

        let tenant_id = match self.resolve_tenant_id(plan_id, step, ctx).await {
            Ok(id) => id,
            Err(reason) => {
                counter!("pf_broker_denies_total", 1, "reason" => "missing_tenant");
                return Ok(ToolResult {
                    success: false,
                    result: None,
                    error: Some(reason),
                    execution_id,
                    timestamp,
                });
            }
        };

        let rate_limit_decision = self
            .rate_limiter
            .check_rate_limit(&tenant_id, &step.tool, &execution_id)
            .await?;

        match rate_limit_decision {
            RateLimitDecision::Allow => {}
            RateLimitDecision::Deny(reason) => {
                let usage = self
                    .rate_limiter
                    .get_current_usage(&tenant_id, &step.tool)
                    .await?;
                self.rate_limiter
                    .log_violation(
                        &tenant_id,
                        &step.tool,
                        "RATE_LIMIT_EXCEEDED",
                        &reason,
                        &usage,
                    )
                    .await?;

                counter!("pf_broker_denies_total", 1, "reason" => "rate_limit");

                return Ok(ToolResult {
                    success: false,
                    result: None,
                    error: Some(format!("Rate limit exceeded: {}", reason)),
                    execution_id,
                    timestamp,
                });
            }
            RateLimitDecision::RequireApproval(reason) => {
                let risk_score = self.risk_score_for_tool(&step.tool);
                let approval_request = approvals::ToolCall {
                    call_id: execution_id.clone(),
                    session_id: format!("{}:{}", tenant_id, plan_id),
                    tool_name: step.tool.clone(),
                    parameters: step.args.clone(),
                    risk_score,
                    kernel_decision: None,
                    timestamp: Utc::now().to_rfc3339(),
                };

                let approval_id = self
                    .approval_manager
                    .create_approval_request(approval_request, risk_score, reason.clone())
                    .await?;

                counter!("pf_broker_approvals_required_total", 1, "tool" => step.tool.clone());

                return Ok(ToolResult {
                    success: false,
                    result: None,
                    error: Some(format!("Approval required: {} (ID: {})", reason, approval_id)),
                    execution_id,
                    timestamp,
                });
            }
            RateLimitDecision::Throttle(delay_ms) => {
                info!(
                    "Tool execution throttled for {}ms (tenant={}, tool={})",
                    delay_ms, tenant_id, step.tool
                );
                let slept = Self::apply_throttle_delay(delay_ms).await;
                histogram!(
                    "pf_broker_throttle_delay_seconds",
                    slept.as_secs_f64()
                );
            }
        }

        match step.tool.as_str() {
            "retrieval" => {
                if let Some(ref receipts) = step.receipts {
                    for receipt in receipts {
                        self.verify_receipt(receipt)?;
                    }
                }

                Ok(ToolResult {
                    success: true,
                    result: Some(serde_json::json!({
                        "type": "retrieval_result",
                        "documents": ["doc1", "doc2"],
                        "execution_id": execution_id,
                        "tenant_id": tenant_id
                    })),
                    error: None,
                    execution_id,
                    timestamp,
                })
            }
            "search" => Ok(ToolResult {
                success: true,
                result: Some(serde_json::json!({
                    "type": "search_result",
                    "results": ["result1", "result2"],
                    "execution_id": execution_id,
                    "tenant_id": tenant_id
                })),
                error: None,
                execution_id,
                timestamp,
            }),
            "email" => Ok(ToolResult {
                success: true,
                result: Some(serde_json::json!({
                    "type": "email_sent",
                    "recipient": step.args.get("to"),
                    "execution_id": execution_id,
                    "tenant_id": tenant_id
                })),
                error: None,
                execution_id,
                timestamp,
            }),
            _ => Ok(ToolResult {
                success: true,
                result: Some(serde_json::json!({
                    "type": "tool_result",
                    "tool": step.tool,
                    "execution_id": execution_id,
                    "tenant_id": tenant_id
                })),
                error: None,
                execution_id,
                timestamp,
            }),
        }
    }

    fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<()> {
        pf_dsse::verify_access_receipt(
            &pf_dsse::AccessReceiptPayload {
                receipt_id: receipt.receipt_id.clone(),
                tenant: receipt.tenant.clone(),
                subject_id: receipt.subject_id.clone(),
                query_hash: receipt.query_hash.clone(),
                index_shard: receipt.index_shard.clone(),
                timestamp: receipt.timestamp,
                result_hash: receipt.result_hash.clone(),
                result_count: 0,
                query_time_ms: 0,
                signature: String::new(),
            },
            &receipt.sign_alg,
            &receipt.sig,
        )
        .map_err(|e| anyhow::anyhow!(e.to_string()))?;

        info!("Receipt verified: {}", receipt.receipt_id);
        Ok(())
    }

    async fn get_violations(&self) -> Vec<Violation> {
        let violations = self.violation_log.read().await;
        violations.clone()
    }

    pub async fn get_rate_limit_stats(&self) -> Result<HashMap<String, u32>> {
        self.rate_limiter.get_violation_stats().await
    }

    pub async fn update_rate_limit_config(&mut self, new_config: RateLimitConfig) -> Result<()> {
        self.rate_limiter.update_config(new_config).await
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let kernel_url =
        std::env::var("KERNEL_URL").unwrap_or_else(|_| "http://localhost:8006".to_string());
    let broker = ToolBroker::new(kernel_url.clone());

    info!("Tool broker started with kernel URL: {}", kernel_url);

    let plan_json = r#"{
        "plan_id": "test-plan-1",
        "tenant": "tenant-1",
        "subject": {
            "id": "user-1",
            "caps": ["read_docs", "send_email"]
        },
        "steps": [
            {
                "tool": "retrieval",
                "args": {"query": "test"},
                "caps_required": ["read_docs"],
                "labels_in": [],
                "labels_out": ["docs"]
            }
        ],
        "constraints": {
            "budget": 10.0,
            "pii": false,
            "dp_epsilon": 1.0
        },
        "system_prompt_hash": "a1b2c3d4e5f6..."
    }"#;

    let decision = broker.submit_plan(plan_json).await?;
    println!("Kernel decision: {:?}", decision);

    let tool_call = ToolCall {
        tool: "retrieval".to_string(),
        args: HashMap::new(),
        step_index: Some(0),
    };

    let result = broker.execute_tool(&tool_call, "test-plan-1").await?;
    println!("Tool execution result: {:?}", result);

    let unapproved_call = ToolCall {
        tool: "unauthorized_tool".to_string(),
        args: HashMap::new(),
        step_index: Some(1),
    };

    let unapproved_result = broker.execute_tool(&unapproved_call, "test-plan-1").await?;
    println!("Unapproved tool result: {:?}", unapproved_result);

    let violations = broker.get_violations().await;
    println!("Violations: {:?}", violations);

    println!("Testing rate limiting...");

    let rate_limit_stats = broker.get_rate_limit_stats().await?;
    println!("Rate limit violations: {:?}", rate_limit_stats);

    for i in 0..150 {
        let test_call = ToolCall {
            tool: "data_query".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        let result = broker.execute_tool(&test_call, "test-plan-1").await?;
        if !result.success {
            println!("Rate limit triggered at call {}: {:?}", i, result.error);
            break;
        }
    }

    let final_stats = broker.get_rate_limit_stats().await?;
    println!("Final rate limit violations: {:?}", final_stats);

    Ok(())
}

#[cfg(test)]
mod wave10_tests {
    use super::*;
    use base64::{engine::general_purpose::URL_SAFE_NO_PAD, Engine as _};
    use ratelimit::{TenantRateLimit, ToolRateLimit};
    use std::sync::OnceLock;
    use tokio::sync::{Mutex, MutexGuard};

    /// Serialize tests that mutate process-global `PF_ENFORCE_TENANT`.
    async fn tenant_env_lock() -> MutexGuard<'static, ()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(())).lock().await
    }

    fn make_step(tool: &str) -> ApprovedStep {
        ApprovedStep {
            step_index: 0,
            tool: tool.to_string(),
            args: HashMap::new(),
            receipts: None,
        }
    }

    #[tokio::test]
    async fn tenant_isolation_across_plans() {
        let broker = ToolBroker::new("http://localhost:8080".to_string());

        let mut config = RateLimitConfig::default();
        config.tool_limits.insert(
            "shared_tool".to_string(),
            ToolRateLimit {
                tool_name: "shared_tool".to_string(),
                requests_per_minute: 2,
                requests_per_hour: 100,
                requests_per_day: 1000,
                burst_multiplier: 1.0,
                requires_approval_above: 100,
                cost_per_request: 1.0,
                risk_score: 0.4,
            },
        );
        // Rebuild limiter with config via update on a mut broker
        let mut broker = broker;
        broker.update_rate_limit_config(config).await.unwrap();

        broker
            .install_approved_plan(
                "plan-a",
                Some("tenant-a".to_string()),
                vec![make_step("shared_tool")],
            )
            .await;
        broker
            .install_approved_plan(
                "plan-b",
                Some("tenant-b".to_string()),
                vec![make_step("shared_tool")],
            )
            .await;

        let call = ToolCall {
            tool: "shared_tool".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        assert!(broker.execute_tool(&call, "plan-a").await.unwrap().success);
        assert!(broker.execute_tool(&call, "plan-a").await.unwrap().success);
        let denied_a = broker.execute_tool(&call, "plan-a").await.unwrap();
        assert!(!denied_a.success);
        assert!(
            denied_a
                .error
                .as_deref()
                .unwrap_or("")
                .contains("Rate limit"),
            "tenant-a should be denied after exhausting its window"
        );

        let ok_b = broker.execute_tool(&call, "plan-b").await.unwrap();
        assert!(
            ok_b.success,
            "tenant-b must remain isolated from tenant-a usage"
        );
    }

    #[tokio::test]
    async fn throttle_delay_is_applied() {
        let slept = ToolBroker::apply_throttle_delay(40).await;
        assert!(
            slept >= Duration::from_millis(35),
            "expected throttle sleep >= 35ms, got {:?}",
            slept
        );

        let mut config = RateLimitConfig::default();
        config.throttle_delay_ms = 30;
        config.tool_limits.insert(
            "soft_tool".to_string(),
            ToolRateLimit {
                tool_name: "soft_tool".to_string(),
                requests_per_minute: 1,
                requests_per_hour: 100,
                requests_per_day: 1000,
                burst_multiplier: 5.0,
                requires_approval_above: 100,
                cost_per_request: 0.1,
                risk_score: 0.2,
            },
        );

        let mut broker = ToolBroker::new("http://localhost:8080".to_string());
        broker.update_rate_limit_config(config).await.unwrap();
        broker
            .install_approved_plan(
                "plan-throttle",
                Some("throttle-tenant".to_string()),
                vec![make_step("soft_tool")],
            )
            .await;

        let call = ToolCall {
            tool: "soft_tool".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        assert!(broker
            .execute_tool(&call, "plan-throttle")
            .await
            .unwrap()
            .success);

        let start = Instant::now();
        let result = broker
            .execute_tool(&call, "plan-throttle")
            .await
            .unwrap();
        let elapsed = start.elapsed();
        assert!(result.success);
        assert!(
            elapsed >= Duration::from_millis(25),
            "throttle branch should sleep; elapsed {:?}",
            elapsed
        );
    }

    #[tokio::test]
    async fn budget_exceed_denies_execution() {
        let mut config = RateLimitConfig::default();
        config.tool_limits.insert(
            "pricey".to_string(),
            ToolRateLimit {
                tool_name: "pricey".to_string(),
                requests_per_minute: 1000,
                requests_per_hour: 10000,
                requests_per_day: 100000,
                burst_multiplier: 2.0,
                requires_approval_above: 500,
                cost_per_request: 10.0,
                risk_score: 0.6,
            },
        );
        config.tenant_limits.insert(
            "budget-tenant".to_string(),
            TenantRateLimit {
                tenant_id: "budget-tenant".to_string(),
                total_requests_per_minute: 1000,
                total_requests_per_hour: 10000,
                total_requests_per_day: 100000,
                budget_per_minute: 10.0,
                budget_per_hour: 100.0,
                budget_per_day: 1000.0,
            },
        );

        let mut broker = ToolBroker::new("http://localhost:8080".to_string());
        broker.update_rate_limit_config(config).await.unwrap();
        broker
            .install_approved_plan(
                "plan-budget",
                Some("budget-tenant".to_string()),
                vec![make_step("pricey")],
            )
            .await;

        let call = ToolCall {
            tool: "pricey".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        assert!(broker
            .execute_tool(&call, "plan-budget")
            .await
            .unwrap()
            .success);

        let denied = broker.execute_tool(&call, "plan-budget").await.unwrap();
        assert!(!denied.success);
        let err = denied.error.unwrap_or_default();
        assert!(
            err.to_ascii_lowercase().contains("budget"),
            "expected budget deny, got {}",
            err
        );
    }

    #[tokio::test]
    async fn missing_tenant_denied_by_default() {
        let _guard = tenant_env_lock().await;
        std::env::remove_var("PF_ENFORCE_TENANT");
        let broker = ToolBroker::new("http://localhost:8080".to_string());
        broker
            .install_approved_plan("plan-no-tenant", None, vec![make_step("retrieval")])
            .await;

        let call = ToolCall {
            tool: "retrieval".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        let result = broker.execute_tool(&call, "plan-no-tenant").await.unwrap();

        assert!(!result.success);
        assert!(
            result
                .error
                .as_deref()
                .unwrap_or("")
                .contains("missing tenant_id"),
            "expected missing-tenant deny when PF_ENFORCE_TENANT unset"
        );
    }

    #[tokio::test]
    async fn missing_tenant_allowed_when_opted_out() {
        let _guard = tenant_env_lock().await;
        std::env::set_var("PF_ENFORCE_TENANT", "0");
        let broker = ToolBroker::new("http://localhost:8080".to_string());
        broker
            .install_approved_plan("plan-opt-out", None, vec![make_step("retrieval")])
            .await;

        let call = ToolCall {
            tool: "retrieval".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };

        let result = broker.execute_tool(&call, "plan-opt-out").await.unwrap();
        std::env::remove_var("PF_ENFORCE_TENANT");

        assert!(result.success);
        assert_eq!(
            result
                .result
                .as_ref()
                .and_then(|v| v.get("tenant_id"))
                .and_then(|v| v.as_str()),
            Some("default_tenant")
        );
    }

    #[tokio::test]
    async fn unverified_jwt_does_not_bind_tenant() {
        let _guard = tenant_env_lock().await;
        // Spoofable unsigned JWT payload must not authorize tenant binding.
        let payload = URL_SAFE_NO_PAD.encode(br#"{"tenant_id":"spoofed-tenant"}"#);
        let jwt = format!("e30.{}.sig", payload);

        std::env::remove_var("PF_ENFORCE_TENANT");
        let broker = ToolBroker::new("http://localhost:8080".to_string());
        broker
            .install_approved_plan("plan-jwt-spoof", None, vec![make_step("retrieval")])
            .await;

        let call = ToolCall {
            tool: "retrieval".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };
        let ctx = ExecutionContext {
            tenant_id: None,
            jwt: Some(jwt),
        };

        let result = broker
            .execute_tool_with_context(&call, "plan-jwt-spoof", Some(&ctx))
            .await
            .unwrap();

        assert!(!result.success);
        assert!(
            result
                .error
                .as_deref()
                .unwrap_or("")
                .contains("missing tenant_id"),
            "unverified JWT must not supply tenant"
        );
    }

    #[tokio::test]
    async fn verified_tenant_id_on_context_binds() {
        let _guard = tenant_env_lock().await;
        std::env::remove_var("PF_ENFORCE_TENANT");
        let broker = ToolBroker::new("http://localhost:8080".to_string());
        broker
            .install_approved_plan("plan-ctx-tenant", None, vec![make_step("retrieval")])
            .await;

        let call = ToolCall {
            tool: "retrieval".to_string(),
            args: HashMap::new(),
            step_index: Some(0),
        };
        let ctx = ExecutionContext {
            tenant_id: Some("verified-tenant".to_string()),
            jwt: None,
        };

        let result = broker
            .execute_tool_with_context(&call, "plan-ctx-tenant", Some(&ctx))
            .await
            .unwrap();

        assert!(result.success);
        assert_eq!(
            result
                .result
                .as_ref()
                .and_then(|v| v.get("tenant_id"))
                .and_then(|v| v.as_str()),
            Some("verified-tenant")
        );
    }

    #[tokio::test]
    async fn tenant_enforced_default_and_opt_out() {
        let _guard = tenant_env_lock().await;
        std::env::remove_var("PF_ENFORCE_TENANT");
        assert!(ToolBroker::tenant_enforced(), "unset must enforce");
        std::env::set_var("PF_ENFORCE_TENANT", "1");
        assert!(ToolBroker::tenant_enforced());
        std::env::set_var("PF_ENFORCE_TENANT", "0");
        assert!(!ToolBroker::tenant_enforced());
        std::env::set_var("PF_ENFORCE_TENANT", "false");
        assert!(!ToolBroker::tenant_enforced());
        std::env::remove_var("PF_ENFORCE_TENANT");
    }

    #[test]
    fn risk_score_from_allow_list_metadata() {
        let broker = ToolBroker::new("http://localhost:8080".to_string());
        assert!((broker.risk_score_for_tool("retrieval") - 0.3).abs() < f64::EPSILON);
        assert!((broker.risk_score_for_tool("email") - 0.7).abs() < f64::EPSILON);
        assert!((broker.risk_score_for_tool("unknown_tool") - 0.9).abs() < f64::EPSILON);
    }
}
