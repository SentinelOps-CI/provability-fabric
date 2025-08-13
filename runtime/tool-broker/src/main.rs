use anyhow::{Context, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tracing::{info, warn, error};
use metrics::{counter, histogram, gauge};
use uuid::Uuid;
use chrono::{DateTime, Utc};

mod ratelimit;
mod approvals;

#[cfg(test)]
mod ratelimit_test;
#[cfg(test)]
mod integration_test;

use ratelimit::{RateLimiter, RateLimitConfig, RateLimitDecision, RateLimitUsage};
use approvals::ApprovalManager;

#[derive(Debug, Deserialize, Serialize)]
struct KernelDecision {
    approved_steps: Vec<ApprovedStep>,
    reason: String,
    valid: bool,
    errors: Option<Vec<String>>,
    warnings: Option<Vec<String>>,
}

#[derive(Debug, Deserialize, Serialize)]
struct ApprovedStep {
    step_index: usize,
    tool: String,
    args: HashMap<String, serde_json::Value>,
    receipts: Option<Vec<AccessReceipt>>,
}

#[derive(Debug, Deserialize, Serialize)]
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

#[derive(Debug, Deserialize, Serialize)]
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

#[derive(Debug, Serialize)]
struct Violation {
    violation_type: String,
    reason: String,
    tool_call: ToolCall,
    timestamp: DateTime<Utc>,
}

struct ToolBroker {
    kernel_url: String,
    http_client: reqwest::Client,
    approved_steps: Arc<RwLock<HashMap<String, Vec<ApprovedStep>>>>,
    violation_log: Arc<RwLock<Vec<Violation>>>,
    rate_limiter: RateLimiter,
    approval_manager: ApprovalManager,
}

impl ToolBroker {
    pub fn new(kernel_url: String) -> Self {
        // Create optimized HTTP client with connection pooling
        let http_client = reqwest::Client::builder()
            .pool_max_idle_per_host(10) // Optimize for typical load
            .pool_idle_timeout(Duration::from_secs(30)) // Keep connections alive
            .http2_prior_knowledge() // Force HTTP/2 for better performance
            .timeout(Duration::from_secs(30)) // Request timeout
            .connect_timeout(Duration::from_secs(10)) // Connection timeout
            .tcp_keepalive(Some(Duration::from_secs(30))) // TCP keepalive
            .build()
            .expect("Failed to create HTTP client");

        // Initialize rate limiter with default configuration
        let rate_limiter = RateLimiter::new(RateLimitConfig::default());
        
        // Initialize approval manager with default configuration
        let approval_manager = ApprovalManager::new(approvals::ApprovalConfig::default());

        Self {
            kernel_url,
            http_client,
            approved_steps: Arc::new(RwLock::new(HashMap::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
            rate_limiter,
            approval_manager,
        }
    }

    async fn submit_plan(&self, plan_json: &str) -> Result<KernelDecision> {
        let start_time = std::time::Instant::now();
        
        // Record connection pool metrics
        let pool_status = self.http_client.get_pool_status();
        gauge!("http_connection_pool_size", pool_status.idle_connections as f64);
        gauge!("http_connection_pool_available", pool_status.available_connections as f64);
        
        let response = self
            .http_client
            .post(&format!("{}/approve", self.kernel_url))
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
            let mut approved_steps = self.approved_steps.write().await;
            approved_steps.insert(plan_id, decision.approved_steps.clone());
            info!("Plan approved with {} steps", decision.approved_steps.len());
            counter!("plans_approved_total", 1);
        } else {
            warn!("Plan rejected: {}", decision.reason);
            counter!("plans_rejected_total", 1);
        }

        Ok(decision)
    }

    fn extract_plan_id(&self, plan_json: &str) -> Result<String> {
        let plan: serde_json::Value = serde_json::from_str(plan_json)
            .context("Failed to parse plan JSON")?;
        
        plan.get("plan_id")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string())
            .ok_or_else(|| anyhow::anyhow!("Plan ID not found"))
    }

    async fn execute_tool(&self, tool_call: &ToolCall, plan_id: &str) -> Result<ToolResult> {
        let start_time = std::time::Instant::now();
        let execution_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();

        // Check if this tool call is approved
        let approved_steps = self.approved_steps.read().await;
        let plan_steps = approved_steps.get(plan_id);

        match plan_steps {
            Some(steps) => {
                // Find the approved step that matches this tool call
                let approved_step = steps.iter().find(|step| {
                    step.tool == tool_call.tool && 
                    step.step_index == tool_call.step_index.unwrap_or(0)
                });

                match approved_step {
                    Some(step) => {
                        // Execute the approved tool
                        let result = self.execute_approved_tool(tool_call, step).await?;
                        
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
                        violation_log.push(violation.clone());
                        
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
                violation_log.push(violation.clone());
                
                counter!("tool_violations_total", 1);
                
                Err(anyhow::anyhow!("No approved plan found"))
            }
        }
    }

    async fn execute_approved_tool(&self, tool_call: &ToolCall, step: &ApprovedStep) -> Result<ToolResult> {
        let execution_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();

        // Extract tenant from plan (simplified - in real implementation would come from context)
        let tenant_id = "default_tenant"; // TODO: Extract from plan or context
        
        // Check rate limits before execution
        let rate_limit_decision = self.rate_limiter.check_rate_limit(
            tenant_id,
            &step.tool,
            &execution_id
        ).await?;

        match rate_limit_decision {
            RateLimitDecision::Allow => {
                // Continue with execution
            }
            RateLimitDecision::Deny(reason) => {
                // Log violation and return error
                let usage = self.rate_limiter.get_current_usage(tenant_id, &step.tool).await?;
                self.rate_limiter.log_violation(
                    tenant_id,
                    &step.tool,
                    "RATE_LIMIT_EXCEEDED",
                    &reason,
                    &usage
                ).await?;
                
                // Record metrics
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
                // Create approval request
                let approval_request = approvals::ToolCall {
                    call_id: execution_id.clone(),
                    session_id: "default_session".to_string(),
                    tool_name: step.tool.clone(),
                    parameters: step.args.clone(),
                    risk_score: 0.7, // TODO: Calculate based on tool and context
                    kernel_decision: None,
                    timestamp: Utc::now().to_rfc3339(),
                };
                
                let approval_id = self.approval_manager.create_approval_request(
                    approval_request,
                    0.7,
                    reason.clone()
                ).await?;
                
                // Record metrics
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
                // TODO: Implement throttling with delay
                info!("Tool execution throttled for {}ms", delay_ms);
            }
        }

        // Simulate tool execution based on tool type
        match step.tool.as_str() {
            "retrieval" => {
                // Verify receipts if present
                if let Some(ref receipts) = step.receipts {
                    for receipt in receipts {
                        self.verify_receipt(receipt)?;
                    }
                }
                
                // Simulate retrieval result
                Ok(ToolResult {
                    success: true,
                    result: Some(serde_json::json!({
                        "type": "retrieval_result",
                        "documents": ["doc1", "doc2"],
                        "execution_id": execution_id
                    })),
                    error: None,
                    execution_id,
                    timestamp,
                })
            }
            "search" => {
                // Simulate search result
                Ok(ToolResult {
                    success: true,
                    result: Some(serde_json::json!({
                        "type": "search_result",
                        "results": ["result1", "result2"],
                        "execution_id": execution_id
                    })),
                    error: None,
                    execution_id,
                    timestamp,
                })
            }
            "email" => {
                // Simulate email sending
                Ok(ToolResult {
                    success: true,
                    result: Some(serde_json::json!({
                        "type": "email_sent",
                        "recipient": step.args.get("to"),
                        "execution_id": execution_id
                    })),
                    error: None,
                    execution_id,
                    timestamp,
                })
            }
            _ => {
                // Generic tool execution
                Ok(ToolResult {
                    success: true,
                    result: Some(serde_json::json!({
                        "type": "tool_result",
                        "tool": step.tool,
                        "execution_id": execution_id
                    })),
                    error: None,
                    execution_id,
                    timestamp,
                })
            }
        }
    }

    fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<()> {
        // Basic receipt validation
        if receipt.receipt_id.is_empty() {
            return Err(anyhow::anyhow!("Receipt ID is empty"));
        }
        if receipt.tenant.is_empty() {
            return Err(anyhow::anyhow!("Receipt tenant is empty"));
        }
        if receipt.sig.is_empty() {
            return Err(anyhow::anyhow!("Receipt signature is empty"));
        }

        // TODO: Implement actual signature verification
        // For now, just validate structure
        info!("Receipt verified: {}", receipt.receipt_id);
        Ok(())
    }

    async fn get_violations(&self) -> Vec<Violation> {
        let violations = self.violation_log.read().await;
        violations.clone()
    }

    /// Get rate limit violation statistics
    pub async fn get_rate_limit_stats(&self) -> Result<HashMap<String, u32>> {
        self.rate_limiter.get_violation_stats().await
    }

    /// Update rate limit configuration
    pub async fn update_rate_limit_config(&mut self, new_config: RateLimitConfig) -> Result<()> {
        self.rate_limiter.update_config(new_config).await
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    let kernel_url = std::env::var("KERNEL_URL").unwrap_or_else(|_| "http://localhost:8080".to_string());
    let broker = ToolBroker::new(kernel_url);

    info!("Tool broker started with kernel URL: {}", kernel_url);

    // Example usage
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

    // Submit plan to kernel
    let decision = broker.submit_plan(plan_json).await?;
    println!("Kernel decision: {:?}", decision);

    // Try to execute an approved tool
    let tool_call = ToolCall {
        tool: "retrieval".to_string(),
        args: HashMap::new(),
        step_index: Some(0),
    };

    let result = broker.execute_tool(&tool_call, "test-plan-1").await?;
    println!("Tool execution result: {:?}", result);

    // Try to execute an unapproved tool
    let unapproved_call = ToolCall {
        tool: "unauthorized_tool".to_string(),
        args: HashMap::new(),
        step_index: Some(1),
    };

    let unapproved_result = broker.execute_tool(&unapproved_call, "test-plan-1").await?;
    println!("Unapproved tool result: {:?}", unapproved_result);

    // Get violations
    let violations = broker.get_violations().await;
    println!("Violations: {:?}", violations);

    // Test rate limiting
    println!("Testing rate limiting...");
    
    // Get rate limit stats
    let rate_limit_stats = broker.get_rate_limit_stats().await?;
    println!("Rate limit violations: {:?}", rate_limit_stats);

    // Test multiple rapid calls to trigger rate limiting
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

    // Get final rate limit stats
    let final_stats = broker.get_rate_limit_stats().await?;
    println!("Final rate limit violations: {:?}", final_stats);

    Ok(())
} 