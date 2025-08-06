use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::fs;

/// ABAC policy configuration
#[derive(Debug, Clone, Deserialize)]
pub struct AbacPolicy {
    pub version: String,
    pub description: String,
    pub default_policy: String,
    pub tenant_isolation: TenantIsolation,
    pub label_policies: Vec<LabelPolicy>,
    pub subject_rules: Vec<SubjectRule>,
    pub capabilities: HashMap<String, CapabilityConfig>,
    pub query_context: QueryContextConfig,
    pub audit: AuditConfig,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TenantIsolation {
    pub enabled: bool,
    pub strict_mode: bool,
    pub cross_tenant_queries: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LabelPolicy {
    pub label: String,
    pub access_rule: String,
    pub description: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SubjectRule {
    pub subject_pattern: String,
    pub privileges: Option<Vec<String>>,
    pub capabilities: Option<Vec<String>>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CapabilityConfig {
    pub description: String,
    pub required_for: Vec<String>,
    pub dp_budget_required: Option<bool>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct QueryContextConfig {
    pub rate_limits: Vec<RateLimit>,
    pub complexity_limits: ComplexityLimits,
}

#[derive(Debug, Clone, Deserialize)]
pub struct RateLimit {
    pub scope: String,
    pub requests_per_minute: u32,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ComplexityLimits {
    pub max_query_length: usize,
    pub max_results_per_query: usize,
    pub max_concurrent_queries: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct AuditConfig {
    pub always_audit: Vec<String>,
    pub query_logging: QueryLogging,
}

#[derive(Debug, Clone, Deserialize)]
pub struct QueryLogging {
    pub enabled: bool,
    pub log_query_text: bool,
    pub log_query_hash: bool,
    pub log_result_count: bool,
    pub log_timing: bool,
}

/// Query context for ABAC evaluation
#[derive(Debug, Clone)]
pub struct QueryContext {
    pub tenant: String,
    pub subject_id: String,
    pub labels_filter: Vec<String>,
    pub query_hash: String,
}

/// ABAC authorization decision
#[derive(Debug, Clone, Serialize)]
pub struct AuthorizationDecision {
    pub allowed: bool,
    pub reason: Option<String>,
    pub rules_applied: Vec<String>,
    pub audit_required: bool,
}

impl AbacPolicy {
    /// Load ABAC policy from YAML file
    pub async fn load_from_file(path: &str) -> Result<Self> {
        let content = fs::read_to_string(path)
            .await
            .context("Failed to read ABAC policy file")?;
        
        let policy: AbacPolicy = serde_yaml::from_str(&content)
            .context("Failed to parse ABAC policy YAML")?;
            
        Ok(policy)
    }

    /// Authorize a query based on context and policies
    pub async fn authorize_query(&self, context: &QueryContext) -> Result<bool> {
        let decision = self.evaluate_query(context).await?;
        Ok(decision.allowed)
    }

    /// Evaluate query and return detailed decision
    pub async fn evaluate_query(&self, context: &QueryContext) -> Result<AuthorizationDecision> {
        let mut decision = AuthorizationDecision {
            allowed: self.default_policy == "allow",
            reason: None,
            rules_applied: Vec::new(),
            audit_required: false,
        };

        // Check tenant isolation
        if self.tenant_isolation.enabled {
            if !self.check_tenant_isolation(context).await? {
                decision.allowed = false;
                decision.reason = Some("Tenant isolation violation".to_string());
                return Ok(decision);
            }
            decision.rules_applied.push("tenant_isolation".to_string());
        }

        // Check subject rules
        if let Some(subject_rule) = self.find_matching_subject_rule(&context.subject_id) {
            decision.rules_applied.push(format!("subject_rule:{}", subject_rule.subject_pattern));
        }

        // Check label policies
        for label in &context.labels_filter {
            if let Some(label_policy) = self.find_label_policy(label) {
                let label_allowed = self.evaluate_label_access(context, label_policy).await?;
                if !label_allowed {
                    decision.allowed = false;
                    decision.reason = Some(format!("Label '{}' access denied", label));
                    return Ok(decision);
                }
                decision.rules_applied.push(format!("label_policy:{}", label));

                // Check if audit required
                if self.audit.always_audit.contains(label) || 
                   self.audit.always_audit.iter().any(|pattern| label.contains(pattern)) {
                    decision.audit_required = true;
                }
            }
        }

        // If we get here and default is deny, check if any allow rules matched
        if self.default_policy == "deny" && !decision.rules_applied.is_empty() {
            decision.allowed = true;
        }

        Ok(decision)
    }

    /// Check tenant isolation rules
    async fn check_tenant_isolation(&self, context: &QueryContext) -> Result<bool> {
        if self.tenant_isolation.strict_mode {
            // In strict mode, only allow queries within the same tenant
            // This would be validated against the index shard mapping
            return Ok(!context.tenant.is_empty());
        }
        Ok(true)
    }

    /// Find matching subject rule
    fn find_matching_subject_rule(&self, subject_id: &str) -> Option<&SubjectRule> {
        self.subject_rules.iter().find(|rule| {
            if rule.subject_pattern == "*" {
                true
            } else if rule.subject_pattern.ends_with('*') {
                let prefix = &rule.subject_pattern[..rule.subject_pattern.len() - 1];
                subject_id.starts_with(prefix)
            } else {
                subject_id == rule.subject_pattern
            }
        })
    }

    /// Find label policy
    fn find_label_policy(&self, label: &str) -> Option<&LabelPolicy> {
        self.label_policies.iter().find(|policy| policy.label == label)
    }

    /// Evaluate label access
    async fn evaluate_label_access(&self, context: &QueryContext, policy: &LabelPolicy) -> Result<bool> {
        // Simplified rule evaluation - in real implementation would use a proper policy engine
        match policy.access_rule.as_str() {
            "false" => Ok(false),
            "true" => Ok(true),
            "tenant_match" => Ok(!context.tenant.is_empty()),
            rule if rule.contains("tenant_match") => {
                // Complex rule with tenant_match requirement
                Ok(!context.tenant.is_empty())
            }
            rule if rule.contains("capability:") => {
                // Would check capability token for required capability
                // For now, assume granted if subject is not empty
                Ok(!context.subject_id.is_empty())
            }
            _ => {
                // Default to allow for unknown rules (would be more strict in production)
                Ok(true)
            }
        }
    }

    /// Check if query should be audited
    pub fn should_audit(&self, context: &QueryContext) -> bool {
        // Check if any labels require auditing
        context.labels_filter.iter().any(|label| {
            self.audit.always_audit.contains(label) || 
            self.audit.always_audit.iter().any(|pattern| 
                pattern.starts_with("label:") && label == &pattern[6:]
            )
        })
    }

    /// Get rate limits for context
    pub fn get_rate_limits(&self, context: &QueryContext) -> Vec<&RateLimit> {
        self.query_context.rate_limits.iter().filter(|limit| {
            match limit.scope.as_str() {
                "tenant" => true,
                "subject" => true,
                scope if scope.starts_with("subject+label:") => {
                    let label = &scope[14..];
                    context.labels_filter.contains(&label.to_string())
                }
                _ => false,
            }
        }).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_tenant_isolation() {
        let policy = create_test_policy();
        let context = QueryContext {
            tenant: "tenant1".to_string(),
            subject_id: "user1".to_string(),
            labels_filter: vec!["public".to_string()],
            query_hash: "test_hash".to_string(),
        };

        let result = policy.check_tenant_isolation(&context).await.unwrap();
        assert!(result);
    }

    #[tokio::test]
    async fn test_subject_rule_matching() {
        let policy = create_test_policy();
        
        let admin_rule = policy.find_matching_subject_rule("admin_user1");
        assert!(admin_rule.is_some());
        assert_eq!(admin_rule.unwrap().subject_pattern, "admin_*");

        let regular_rule = policy.find_matching_subject_rule("regular_user");
        assert!(regular_rule.is_some());
        assert_eq!(regular_rule.unwrap().subject_pattern, "*");
    }

    #[test]
    fn test_audit_requirements() {
        let policy = create_test_policy();
        let context = QueryContext {
            tenant: "tenant1".to_string(),
            subject_id: "user1".to_string(),
            labels_filter: vec!["confidential".to_string()],
            query_hash: "test_hash".to_string(),
        };

        assert!(policy.should_audit(&context));
    }

    fn create_test_policy() -> AbacPolicy {
        AbacPolicy {
            version: "1.0".to_string(),
            description: "Test policy".to_string(),
            default_policy: "deny".to_string(),
            tenant_isolation: TenantIsolation {
                enabled: true,
                strict_mode: true,
                cross_tenant_queries: false,
            },
            label_policies: vec![
                LabelPolicy {
                    label: "public".to_string(),
                    access_rule: "tenant_match".to_string(),
                    description: "Public data".to_string(),
                },
                LabelPolicy {
                    label: "confidential".to_string(),
                    access_rule: "elevated_privileges AND tenant_match".to_string(),
                    description: "Confidential data".to_string(),
                },
            ],
            subject_rules: vec![
                SubjectRule {
                    subject_pattern: "admin_*".to_string(),
                    privileges: Some(vec!["elevated_privileges".to_string()]),
                    capabilities: None,
                },
                SubjectRule {
                    subject_pattern: "*".to_string(),
                    privileges: Some(vec!["basic_access".to_string()]),
                    capabilities: None,
                },
            ],
            capabilities: HashMap::new(),
            query_context: QueryContextConfig {
                rate_limits: vec![
                    RateLimit {
                        scope: "tenant".to_string(),
                        requests_per_minute: 1000,
                    },
                ],
                complexity_limits: ComplexityLimits {
                    max_query_length: 1000,
                    max_results_per_query: 100,
                    max_concurrent_queries: 10,
                },
            },
            audit: AuditConfig {
                always_audit: vec!["confidential".to_string()],
                query_logging: QueryLogging {
                    enabled: true,
                    log_query_text: false,
                    log_query_hash: true,
                    log_result_count: true,
                    log_timing: true,
                },
            },
        }
    }
}