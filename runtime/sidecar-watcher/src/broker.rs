use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{error, info, warn};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, Deserialize, Serialize)]
pub struct KernelDecision {
    pub approved_steps: Vec<ApprovedStep>,
    pub reason: String,
    pub valid: bool,
    pub errors: Option<Vec<String>>,
    pub warnings: Option<Vec<String>>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct ApprovedStep {
    pub step_index: usize,
    pub tool: String,
    pub args: HashMap<String, serde_json::Value>,
    pub receipts: Option<Vec<AccessReceipt>>,
}

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct AccessReceipt {
    pub receipt_id: String,
    pub tenant: String,
    pub subject_id: String,
    pub query_hash: String,
    pub index_shard: String,
    pub timestamp: i64,
    pub result_hash: String,
    pub sign_alg: String,
    pub sig: String,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct ToolCall {
    pub tool: String,
    pub args: HashMap<String, serde_json::Value>,
    pub step_index: Option<usize>,
    pub plan_id: String,
}

#[derive(Debug, Serialize)]
pub struct ToolResult {
    pub success: bool,
    pub result: Option<serde_json::Value>,
    pub error: Option<String>,
    pub execution_id: String,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Serialize)]
pub struct Violation {
    pub violation_type: String,
    pub reason: String,
    pub tool_call: ToolCall,
    pub timestamp: DateTime<Utc>,
}

pub struct BrokerIntegration {
    kernel_url: String,
    http_client: reqwest::Client,
    approved_steps: Arc<RwLock<HashMap<String, Vec<ApprovedStep>>>>,
    violation_log: Arc<RwLock<Vec<Violation>>>,
    enforcement_mode: bool,
}

impl BrokerIntegration {
    pub fn new(kernel_url: String, enforcement_mode: bool) -> Self {
        Self {
            kernel_url,
            http_client: reqwest::Client::new(),
            approved_steps: Arc::new(RwLock::new(HashMap::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
            enforcement_mode,
        }
    }

    pub async fn submit_plan(&self, plan_json: &str) -> Result<KernelDecision> {
        let response = self
            .http_client
            .post(&format!("{}/approve", self.kernel_url))
            .header("Content-Type", "application/json")
            .body(plan_json.to_string())
            .send()
            .await
            .context("Failed to submit plan to kernel")?;

        let decision: KernelDecision = response
            .json()
            .await
            .context("Failed to parse kernel decision")?;

        if decision.valid {
            let plan_id = self.extract_plan_id(plan_json)?;
            let mut approved_steps = self.approved_steps.write().await;
            approved_steps.insert(plan_id, decision.approved_steps.clone());
            info!("Plan approved with {} steps", decision.approved_steps.len());
        } else {
            warn!("Plan rejected: {}", decision.reason);
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

    pub async fn execute_tool(&self, tool_call: &ToolCall) -> Result<ToolResult> {
        let execution_id = Uuid::new_v4().to_string();
        let timestamp = Utc::now();

        if !self.enforcement_mode {
            // In non-enforcement mode, allow all tool calls
            info!("Non-enforcement mode: allowing tool call {}", tool_call.tool);
            return Ok(ToolResult {
                success: true,
                result: Some(serde_json::json!({
                    "type": "tool_result",
                    "tool": tool_call.tool,
                    "execution_id": execution_id,
                    "mode": "non_enforcement"
                })),
                error: None,
                execution_id,
                timestamp,
            });
        }

        // Check if this tool call is approved
        let approved_steps = self.approved_steps.read().await;
        let plan_steps = approved_steps.get(&tool_call.plan_id);

        match plan_steps {
            Some(steps) => {
                // Find the approved step that matches this tool call
                let approved_step = steps.iter().find(|step| {
                    step.tool == tool_call.tool && 
                    step.step_index == tool_call.step_index.unwrap_or(0)
                });

                match approved_step {
                    Some(step) => {
                        info!("Executing approved tool: {}", step.tool);
                        let result = self.execute_approved_tool(step, &execution_id).await?;
                        Ok(ToolResult {
                            success: true,
                            result: Some(result),
                            error: None,
                            execution_id,
                            timestamp,
                        })
                    }
                    None => {
                        let violation = Violation {
                            violation_type: "UNAPPROVED_TOOL".to_string(),
                            reason: format!("Tool '{}' not in approved steps", tool_call.tool),
                            tool_call: tool_call.clone(),
                            timestamp,
                        };

                        {
                            let mut violations = self.violation_log.write().await;
                            violations.push(violation.clone());
                        }

                        error!("Tool execution blocked: {}", violation.reason);
                        Ok(ToolResult {
                            success: false,
                            result: None,
                            error: Some(violation.reason),
                            execution_id,
                            timestamp,
                        })
                    }
                }
            }
            None => {
                let violation = Violation {
                    violation_type: "NO_PLAN_APPROVAL".to_string(),
                    reason: "No approved plan found".to_string(),
                    tool_call: tool_call.clone(),
                    timestamp,
                };

                {
                    let mut violations = self.violation_log.write().await;
                    violations.push(violation.clone());
                }

                error!("Tool execution blocked: {}", violation.reason);
                Ok(ToolResult {
                    success: false,
                    result: None,
                    error: Some(violation.reason),
                    execution_id,
                    timestamp,
                })
            }
        }
    }

    async fn execute_approved_tool(&self, step: &ApprovedStep, execution_id: &str) -> Result<serde_json::Value> {
        // Verify receipts if present
        if let Some(ref receipts) = step.receipts {
            for receipt in receipts {
                self.verify_receipt(receipt)?;
            }
        }
        
        // Simulate tool execution based on tool type
        match step.tool.as_str() {
            "retrieval" => {
                Ok(serde_json::json!({
                    "type": "retrieval_result",
                    "documents": ["doc1", "doc2"],
                    "execution_id": execution_id,
                    "mode": "enforcement"
                }))
            }
            "search" => {
                Ok(serde_json::json!({
                    "type": "search_result",
                    "results": ["result1", "result2"],
                    "execution_id": execution_id,
                    "mode": "enforcement"
                }))
            }
            "email" => {
                Ok(serde_json::json!({
                    "type": "email_sent",
                    "recipient": step.args.get("to"),
                    "execution_id": execution_id,
                    "mode": "enforcement"
                }))
            }
            _ => {
                Ok(serde_json::json!({
                    "type": "tool_result",
                    "tool": step.tool,
                    "execution_id": execution_id,
                    "mode": "enforcement"
                }))
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

    pub async fn get_violations(&self) -> Vec<Violation> {
        let violations = self.violation_log.read().await;
        violations.clone()
    }

    pub fn set_enforcement_mode(&mut self, mode: bool) {
        self.enforcement_mode = mode;
        info!("Enforcement mode set to: {}", mode);
    }

    pub fn is_enforcement_mode(&self) -> bool {
        self.enforcement_mode
    }
} 