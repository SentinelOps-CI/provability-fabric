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
}

impl ToolBroker {
    pub fn new(kernel_url: String) -> Self {
        // Create optimized HTTP client with connection pooling
        let http_client = reqwest::Client::builder()
            .pool_max_idle_per_host(10) // Optimize for typical load
            .pool_idle_timeout(Duration::from_secs(90)) // Keep connections alive
            .http2_prior_knowledge() // Force HTTP/2 for better performance
            .timeout(Duration::from_secs(30)) // Request timeout
            .connect_timeout(Duration::from_secs(10)) // Connection timeout
            .tcp_keepalive(Some(Duration::from_secs(30))) // TCP keepalive
            .build()
            .expect("Failed to create HTTP client");

        Self {
            kernel_url,
            http_client,
            approved_steps: Arc::new(RwLock::new(HashMap::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
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

    Ok(())
} 