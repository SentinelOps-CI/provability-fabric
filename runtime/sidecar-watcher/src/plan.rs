use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use uuid::Uuid;

/// Input channel classification for injection hardening
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InputChannels {
    pub system: SystemChannel,
    pub user: UserChannel,
    pub retrieved: Option<Vec<RetrievedChannel>>,
    pub file: Option<Vec<FileChannel>>,
}

/// Trusted system channel - cannot be modified by untrusted inputs
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemChannel {
    pub hash: String,
    pub policy_hash: String,
}

/// Untrusted user channel - must be quoted and cannot alter instructions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserChannel {
    pub content_hash: String,
    pub quoted: bool,
}

/// Untrusted retrieved content - must be quoted and labeled
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetrievedChannel {
    pub receipt_id: String,
    pub content_hash: String,
    pub quoted: bool,
    pub labels: Vec<String>,
}

/// Untrusted file content - must be quoted and typed
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileChannel {
    pub sha256: String,
    pub media_type: String,
    pub quoted: bool,
}

/// Access receipt for retrieval operations
#[derive(Debug, Clone, Serialize, Deserialize)]
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

/// Plan step with tool call and constraints
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlanStep {
    pub tool: String,
    pub args: HashMap<String, serde_json::Value>,
    pub caps_required: Vec<String>,
    pub labels_in: Vec<String>,
    pub labels_out: Vec<String>,
    pub receipts: Option<Vec<AccessReceipt>>,
}

/// Plan constraints
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlanConstraints {
    pub budget: f64,
    pub pii: bool,
    pub dp_epsilon: f64,
    pub dp_delta: Option<f64>,
    pub latency_max: Option<f64>,
}

/// Complete plan structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Plan {
    pub plan_id: String,
    pub tenant: String,
    pub subject: Subject,
    pub input_channels: InputChannels,
    pub steps: Vec<PlanStep>,
    pub constraints: PlanConstraints,
    pub system_prompt_hash: String,
    pub created_at: u64,
    pub expires_at: u64,
}

/// Subject with capabilities
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Subject {
    pub id: String,
    pub caps: Vec<String>,
}

/// Kernel validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum KernelResult {
    Valid,
    Invalid { reason: String },
}

/// Policy kernel for plan validation
pub struct PolicyKernel {
    config: KernelConfig,
    plan_cache: RwLock<HashMap<String, Plan>>,
}

/// Kernel configuration
#[derive(Debug, Clone)]
pub struct KernelConfig {
    pub max_budget: f64,
    pub max_epsilon: f64,
    pub max_latency: f64,
    pub allowed_tenants: Vec<String>,
}

impl PolicyKernel {
    pub fn new(config: KernelConfig) -> Self {
        Self {
            config,
            plan_cache: RwLock::new(HashMap::new()),
        }
    }

    /// Validate a plan against all policy rules
    pub async fn validate_plan(&self, plan: &Plan) -> KernelResult {
        // Check plan expiration
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        if now > plan.expires_at {
            return KernelResult::Invalid {
                reason: "Plan has expired".to_string(),
            };
        }

        // Validate tenant
        if !self.is_valid_tenant(&plan.tenant) {
            return KernelResult::Invalid {
                reason: "Invalid tenant".to_string(),
            };
        }

        // Validate system prompt hash
        if !self.is_valid_hash(&plan.system_prompt_hash) {
            return KernelResult::Invalid {
                reason: "Invalid system prompt hash".to_string(),
            };
        }

        // Validate input channels
        if let KernelResult::Invalid { reason } = self.validate_input_channels(&plan.input_channels, &plan.system_prompt_hash) {
            return KernelResult::Invalid { reason };
        }

        // Validate constraints
        if let KernelResult::Invalid { reason } = self.validate_constraints(&plan.constraints) {
            return KernelResult::Invalid { reason };
        }

        // Validate each step
        for (i, step) in plan.steps.iter().enumerate() {
            if let KernelResult::Invalid { reason } = self.validate_step(&plan.subject, step, i) {
                return KernelResult::Invalid { reason };
            }
        }

        // Validate label flow
        if let KernelResult::Invalid { reason } = self.validate_label_flow(&plan.steps) {
            return KernelResult::Invalid { reason };
        }

        KernelResult::Valid
    }

    /// Validate input channel classification and quoting requirements
    fn validate_input_channels(&self, channels: &InputChannels, system_prompt_hash: &str) -> KernelResult {
        // Validate system channel (trusted)
        if !self.is_valid_hash(&channels.system.hash) {
            return KernelResult::Invalid {
                reason: "Invalid system channel hash".to_string(),
            };
        }
        if !self.is_valid_hash(&channels.system.policy_hash) {
            return KernelResult::Invalid {
                reason: "Invalid system policy hash".to_string(),
            };
        }
        
        // System hash must match the plan's system prompt hash
        if channels.system.hash != system_prompt_hash {
            return KernelResult::Invalid {
                reason: "System channel hash does not match plan system prompt hash".to_string(),
            };
        }

        // Validate user channel (untrusted)
        if !self.is_valid_hash(&channels.user.content_hash) {
            return KernelResult::Invalid {
                reason: "Invalid user content hash".to_string(),
            };
        }
        if !channels.user.quoted {
            return KernelResult::Invalid {
                reason: "User input must be quoted (quoted=true)".to_string(),
            };
        }

        // Validate retrieved channels (untrusted)
        if let Some(retrieved) = &channels.retrieved {
            for (i, retrieved_channel) in retrieved.iter().enumerate() {
                if !self.is_valid_hash(&retrieved_channel.content_hash) {
                    return KernelResult::Invalid {
                        reason: format!("Invalid retrieved content hash at index {}", i),
                    };
                }
                if !retrieved_channel.quoted {
                    return KernelResult::Invalid {
                        reason: format!("Retrieved content at index {} must be quoted (quoted=true)", i),
                    };
                }
                if retrieved_channel.receipt_id.is_empty() {
                    return KernelResult::Invalid {
                        reason: format!("Retrieved content at index {} must have receipt_id", i),
                    };
                }
                if retrieved_channel.labels.is_empty() {
                    return KernelResult::Invalid {
                        reason: format!("Retrieved content at index {} must have labels", i),
                    };
                }
            }
        }

        // Validate file channels (untrusted)
        if let Some(files) = &channels.file {
            for (i, file_channel) in files.iter().enumerate() {
                if !self.is_valid_hash(&file_channel.sha256) {
                    return KernelResult::Invalid {
                        reason: format!("Invalid file SHA256 at index {}", i),
                    };
                }
                if !file_channel.quoted {
                    return KernelResult::Invalid {
                        reason: format!("File content at index {} must be quoted (quoted=true)", i),
                    };
                }
                if file_channel.media_type.is_empty() {
                    return KernelResult::Invalid {
                        reason: format!("File content at index {} must have media_type", i),
                    };
                }
            }
        }

        KernelResult::Valid
    }

    /// Validate plan constraints
    fn validate_constraints(&self, constraints: &PlanConstraints) -> KernelResult {
        if constraints.budget > self.config.max_budget {
            return KernelResult::Invalid {
                reason: format!(
                    "Budget {} exceeds maximum {}",
                    constraints.budget, self.config.max_budget
                ),
            };
        }

        if constraints.dp_epsilon > self.config.max_epsilon {
            return KernelResult::Invalid {
                reason: format!(
                    "DP epsilon {} exceeds maximum {}",
                    constraints.dp_epsilon, self.config.max_epsilon
                ),
            };
        }

        if let Some(latency_max) = constraints.latency_max {
            if latency_max > self.config.max_latency {
                return KernelResult::Invalid {
                    reason: format!(
                        "Latency {} exceeds maximum {}",
                        latency_max, self.config.max_latency
                    ),
                };
            }
        }

        KernelResult::Valid
    }

    /// Validate a single step
    fn validate_step(&self, subject: &Subject, step: &PlanStep, step_index: usize) -> KernelResult {
        // Check capability match
        for required_cap in &step.caps_required {
            if !self.has_capability(&subject.caps, required_cap) {
                return KernelResult::Invalid {
                    reason: format!(
                        "Step {}: missing required capability '{}'",
                        step_index, required_cap
                    ),
                };
            }
        }

        // Validate tool name
        if step.tool.is_empty() {
            return KernelResult::Invalid {
                reason: format!("Step {}: tool name is required", step_index),
            };
        }

        // Validate arguments
        if step.args.is_empty() {
            return KernelResult::Invalid {
                reason: format!("Step {}: arguments are required", step_index),
            };
        }

        // Validate receipts for retrieval steps
        if step.tool == "retrieval" || step.tool == "search" {
            match &step.receipts {
                None => {
                    return KernelResult::Invalid {
                        reason: format!("Step {}: retrieval step requires access receipts", step_index),
                    };
                }
                Some(receipts) => {
                    if receipts.is_empty() {
                        return KernelResult::Invalid {
                            reason: format!("Step {}: retrieval step requires at least one receipt", step_index),
                        };
                    }
                    
                    // Verify each receipt
                    for (i, receipt) in receipts.iter().enumerate() {
                        if let Err(e) = self.verify_receipt(receipt) {
                            return KernelResult::Invalid {
                                reason: format!("Step {}: receipt {} verification failed: {}", step_index, i, e),
                            };
                        }
                    }
                }
            }
        }

        KernelResult::Valid
    }

    /// Validate label flow
    fn validate_label_flow(&self, steps: &[PlanStep]) -> KernelResult {
        let mut available_labels = std::collections::HashSet::new();
        available_labels.insert("".to_string()); // Empty label is always available

        for (i, step) in steps.iter().enumerate() {
            // Check that input labels are available
            for label_in in &step.labels_in {
                if !available_labels.contains(label_in) {
                    return KernelResult::Invalid {
                        reason: format!(
                            "Step {}: input label '{}' not available",
                            i, label_in
                        ),
                    };
                }
            }

            // Add output labels to available set
            for label_out in &step.labels_out {
                available_labels.insert(label_out.clone());
            }
        }

        KernelResult::Valid
    }

    /// Check if subject has a capability
    fn has_capability(&self, subject_caps: &[String], required_cap: &str) -> bool {
        subject_caps.contains(&required_cap.to_string())
    }

    /// Check if tenant is allowed
    fn is_valid_tenant(&self, tenant: &str) -> bool {
        self.config.allowed_tenants.contains(&tenant.to_string())
    }

    /// Validate SHA-256 hash format
    fn is_valid_hash(&self, hash: &str) -> bool {
        if hash.len() != 64 {
            return false;
        }
        hash.chars().all(|c| c.is_ascii_hexdigit())
    }

    /// Verify a signed access receipt
    fn verify_receipt(&self, receipt: &AccessReceipt) -> Result<(), String> {
        // Basic validation
        if receipt.receipt_id.is_empty() {
            return Err("receipt ID is required".to_string());
        }
        if receipt.tenant.is_empty() {
            return Err("receipt tenant is required".to_string());
        }
        if receipt.index_shard.is_empty() {
            return Err("receipt index shard is required".to_string());
        }
        if receipt.sign_alg != "ed25519" {
            return Err(format!("unsupported signature algorithm: {}", receipt.sign_alg));
        }
        if receipt.sig.is_empty() {
            return Err("receipt signature is required".to_string());
        }
        
        // TODO: Implement actual signature verification
        // This would require access to the public keys for each shard
        // For now, we'll do basic structural validation
        
        Ok(())
    }

    /// Cache a validated plan
    pub async fn cache_plan(&self, plan: Plan) {
        let mut cache = self.plan_cache.write().await;
        cache.insert(plan.plan_id.clone(), plan);
    }

    /// Get a cached plan
    pub async fn get_cached_plan(&self, plan_id: &str) -> Option<Plan> {
        let cache = self.plan_cache.read().await;
        cache.get(plan_id).cloned()
    }

    /// Generate a new plan ID
    pub fn generate_plan_id() -> String {
        format!("plan_{}", Uuid::new_v4().to_string().replace("-", ""))
    }
}

/// Plan manager for the sidecar watcher
pub struct PlanManager {
    kernel: PolicyKernel,
}

impl PlanManager {
    pub fn new(kernel: PolicyKernel) -> Self {
        Self { kernel }
    }

    /// Process a plan and validate it
    pub async fn process_plan(&self, plan: Plan) -> Result<(), String> {
        match self.kernel.validate_plan(&plan).await {
            KernelResult::Valid => {
                self.kernel.cache_plan(plan).await;
                Ok(())
            }
            KernelResult::Invalid { reason } => Err(reason),
        }
    }

    /// Check if a tool call is allowed for a plan
    pub async fn is_tool_allowed(&self, plan_id: &str, tool: &str) -> bool {
        if let Some(plan) = self.kernel.get_cached_plan(plan_id).await {
            for step in &plan.steps {
                if step.tool == tool {
                    return true;
                }
            }
        }
        false
    }

    /// Get plan constraints
    pub async fn get_plan_constraints(&self, plan_id: &str) -> Option<PlanConstraints> {
        if let Some(plan) = self.kernel.get_cached_plan(plan_id).await {
            Some(plan.constraints)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_plan_validation() {
        let config = KernelConfig {
            max_budget: 100.0,
            max_epsilon: 1.0,
            max_latency: 30.0,
            allowed_tenants: vec!["acme-corp".to_string()],
        };

        let kernel = PolicyKernel::new(config);

        let plan = Plan {
            plan_id: "test_plan".to_string(),
            tenant: "acme-corp".to_string(),
            subject: Subject {
                id: "user_123".to_string(),
                caps: vec!["read_docs".to_string(), "send_email".to_string()],
            },
            input_channels: InputChannels {
                system: SystemChannel {
                    hash: "a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456".to_string(),
                    policy_hash: "policy_hash_1".to_string(),
                },
                user: UserChannel {
                    content_hash: "user_input_hash".to_string(),
                    quoted: true,
                },
                retrieved: Some(vec![
                    RetrievedChannel {
                        receipt_id: "receipt_1".to_string(),
                        content_hash: "retrieved_content_hash".to_string(),
                        quoted: true,
                        labels: vec!["public".to_string()],
                    },
                ]),
                file: Some(vec![
                    FileChannel {
                        sha256: "file_sha256".to_string(),
                        media_type: "application/pdf".to_string(),
                        quoted: true,
                    },
                ]),
            },
            steps: vec![
                PlanStep {
                    tool: "retrieve_documents".to_string(),
                    args: HashMap::new(),
                    caps_required: vec!["read_docs".to_string()],
                    labels_in: vec!["public".to_string()],
                    labels_out: vec!["documents".to_string()],
                    receipts: Some(vec![
                        AccessReceipt {
                            receipt_id: "receipt_1".to_string(),
                            tenant: "acme-corp".to_string(),
                            subject_id: "user_123".to_string(),
                            query_hash: "query_hash_1".to_string(),
                            index_shard: "shard_1".to_string(),
                            timestamp: SystemTime::now()
                                .duration_since(UNIX_EPOCH)
                                .unwrap()
                                .as_secs(),
                            result_hash: "result_hash_1".to_string(),
                            sign_alg: "ed25519".to_string(),
                            sig: "signature_1".to_string(),
                        },
                    ]),
                },
            ],
            constraints: PlanConstraints {
                budget: 10.0,
                pii: false,
                dp_epsilon: 0.1,
                dp_delta: Some(1e-6),
                latency_max: Some(5.0),
            },
            system_prompt_hash: "a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456".to_string(),
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            expires_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs() + 3600,
        };

        let result = kernel.validate_plan(&plan).await;
        assert!(matches!(result, KernelResult::Valid));
    }

    #[tokio::test]
    async fn test_missing_capability() {
        let config = KernelConfig {
            max_budget: 100.0,
            max_epsilon: 1.0,
            max_latency: 30.0,
            allowed_tenants: vec!["acme-corp".to_string()],
        };

        let kernel = PolicyKernel::new(config);

        let plan = Plan {
            plan_id: "test_plan".to_string(),
            tenant: "acme-corp".to_string(),
            subject: Subject {
                id: "user_123".to_string(),
                caps: vec!["read_docs".to_string()], // Missing send_email capability
            },
            input_channels: InputChannels {
                system: SystemChannel {
                    hash: "a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456".to_string(),
                    policy_hash: "policy_hash_1".to_string(),
                },
                user: UserChannel {
                    content_hash: "user_input_hash".to_string(),
                    quoted: true,
                },
                retrieved: Some(vec![
                    RetrievedChannel {
                        receipt_id: "receipt_1".to_string(),
                        content_hash: "retrieved_content_hash".to_string(),
                        quoted: true,
                        labels: vec!["public".to_string()],
                    },
                ]),
                file: Some(vec![
                    FileChannel {
                        sha256: "file_sha256".to_string(),
                        media_type: "application/pdf".to_string(),
                        quoted: true,
                    },
                ]),
            },
            steps: vec![
                PlanStep {
                    tool: "send_email".to_string(),
                    args: HashMap::new(),
                    caps_required: vec!["send_email".to_string()],
                    labels_in: vec!["documents".to_string()],
                    labels_out: vec!["sent_email".to_string()],
                    receipts: None,
                },
            ],
            constraints: PlanConstraints {
                budget: 10.0,
                pii: false,
                dp_epsilon: 0.1,
                dp_delta: Some(1e-6),
                latency_max: Some(5.0),
            },
            system_prompt_hash: "a1b2c3d4e5f6789012345678901234567890abcdef1234567890abcdef123456".to_string(),
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            expires_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs() + 3600,
        };

        let result = kernel.validate_plan(&plan).await;
        assert!(matches!(result, KernelResult::Invalid { .. }));
    }
} 