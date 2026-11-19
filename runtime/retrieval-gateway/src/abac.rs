use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
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
    pub query: String,
    pub labels_filter: Vec<String>,
    pub query_hash: String,
    pub index_shard: String,
    /// Scopes bound to the request by a verified JWT.
    pub allowed_labels: Vec<String>,
    pub capabilities: Vec<String>,
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
        policy.validate_configuration()?;
        Ok(policy)
    }

    /// Reject unsupported deployment policies at startup.
    ///
    /// Only conjunctions of precisely defined predicates are supported.
    /// Audit and DP budget predicates are understood but deliberately deny
    /// at runtime until real durable enforcement is implemented.
    pub fn validate_configuration(&self) -> Result<()> {
        if self.default_policy != "deny" || !self.tenant_isolation.enabled
            || !self.tenant_isolation.strict_mode
            || self.tenant_isolation.cross_tenant_queries
        {
            anyhow::bail!("Retrieval authorization needs strict tenant isolation and default deny");
        }
        if self.label_policies.is_empty() || self.subject_rules.is_empty() {
            anyhow::bail!("Retrieval authorization rules must be nonempty");
        }
        let mut labels = HashSet::new();
        for rule in &self.label_policies {
            if rule.label.is_empty() || !labels.insert(rule.label.as_str()) {
                anyhow::bail!("Duplicate or empty ABAC label");
            }
            if rule.access_rule.is_empty()
                || rule.access_rule.split(" AND ").any(|predicate| {
                    !matches!(
                        predicate,
                        "true" | "false" | "tenant_match" | "subject_authorized"
                            | "elevated_privileges" | "audit_log" | "dp_budget_available"
                    ) && !(predicate.starts_with("capability:")
                        && self.capabilities.contains_key(&predicate["capability:".len()..]))
                })
            {
                anyhow::bail!("Unsupported ABAC access predicate for {}", rule.label);
            }
        }
        if self.query_context.complexity_limits.max_query_length == 0
            || self.query_context.complexity_limits.max_results_per_query == 0
        {
            anyhow::bail!("Invalid retrieval complexity limits");
        }
        Ok(())
    }

    /// Authorize a request from a verified tenant/subject and explicit scopes.
    pub async fn authorize_query(&self, context: &QueryContext) -> Result<bool> {
        Ok(self.evaluate_query(context).await?.allowed)
    }

    /// Fail closed on any internal error.
    pub async fn evaluate(&self, context: &QueryContext) -> bool {
        self.authorize_query(context).await.unwrap_or(false)
    }

    /// Require an explicit, fully satisfied label rule for every query label.
    pub async fn evaluate_query(&self, context: &QueryContext) -> Result<AuthorizationDecision> {
        let mut decision = AuthorizationDecision {
            allowed: false,
            reason: None,
            rules_applied: vec![format!("policy:{}:{}", self.version, self.description)],
            audit_required: false,
        };
        if !self.check_tenant_isolation(context).await? {
            decision.reason = Some("Tenant isolation violation".into());
            return Ok(decision);
        }
        let limits = &self.query_context.complexity_limits;
        if context.query.trim().is_empty() || context.query.len() > limits.max_query_length {
            decision.reason = Some("Invalid query length".into());
            return Ok(decision);
        }
        if context.labels_filter.is_empty()
            || context.labels_filter.len() > self.label_policies.len()
        {
            decision.reason = Some("Explicit label scope is mandatory".into());
            return Ok(decision);
        }
        let subject_rule = match self.find_matching_subject_rule(&context.subject_id) {
            Some(rule) => rule,
            None => {
                decision.reason = Some("Unrecognized subject".into());
                return Ok(decision);
            }
        };
        decision.rules_applied.push(format!("subject_rule:{}", subject_rule.subject_pattern));
        for label in &context.labels_filter {
            if !context.allowed_labels.iter().any(|scope| scope == label) {
                decision.reason = Some(format!("Label '{label}' absent from signed token scopes"));
                return Ok(decision);
            }
            let Some(rule) = self.find_label_policy(label) else {
                decision.reason = Some(format!("Unknown label '{label}'"));
                return Ok(decision);
            };
            if !self.evaluate_label_access(context, rule, subject_rule) {
                decision.reason = Some(format!("Label '{label}' access denied"));
                return Ok(decision);
            }
            decision.rules_applied.push(format!("label_policy:{label}"));
        }
        decision.audit_required = self.should_audit(context);
        decision.allowed = true;
        Ok(decision)
    }

    async fn check_tenant_isolation(&self, context: &QueryContext) -> Result<bool> {
        Ok(self.tenant_isolation.enabled
            && self.tenant_isolation.strict_mode
            && !self.tenant_isolation.cross_tenant_queries
            && !context.tenant.trim().is_empty()
            && !context.subject_id.trim().is_empty()
            && context.index_shard == format!("shard_{}", context.tenant))
    }

    /// Match the first applicable subject rule (order is significant).
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

    fn find_label_policy(&self, label: &str) -> Option<&LabelPolicy> {
        self.label_policies.iter().find(|rule| rule.label == label)
    }

    /// Evaluate each conjunct literally; no substring or unknown-rule grants.
    fn evaluate_label_access(
        &self, context: &QueryContext, label: &LabelPolicy, subject: &SubjectRule,
    ) -> bool {
        label.access_rule.split(" AND ").all(|predicate| match predicate {
            "true" => true,
            "false" => false,
            "tenant_match" => context.index_shard == format!("shard_{}", context.tenant),
            "subject_authorized" => context.capabilities.iter().any(|x| x == "private_access"),
            "elevated_privileges" => {
                context.capabilities.iter().any(|x| x == "elevated_privileges")
                    && subject.privileges.as_ref().is_some_and(|roles| {
                        roles.iter().any(|x| x == "elevated_privileges")
                    })
            }
            // There is no durable audit or DP-budget enforcement in this
            // service yet. Deny instead of asserting those predicates hold.
            "audit_log" | "dp_budget_available" => false,
            name if name.starts_with("capability:") => {
                let cap = &name["capability:".len()..];
                self.capabilities.contains_key(cap)
                    && context.capabilities.iter().any(|x| x == cap)
            }
            _ => false,
        })
    }

    /// Check if query should be audited
    pub fn should_audit(&self, context: &QueryContext) -> bool {
        // Check if any labels require auditing
        context.labels_filter.iter().any(|label| {
            self.audit.always_audit.contains(label)
                || self.audit.always_audit.iter().any(|pattern| {
                    pattern.strip_prefix("label:") == Some(label.as_str())
                })
        })
    }

    /// Get rate limits for context
    pub fn get_rate_limits(&self, context: &QueryContext) -> Vec<&RateLimit> {
        self.query_context.rate_limits.iter().filter(|limit| {
            let _ = limit.requests_per_minute;
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
            query: "test".to_string(),
            labels_filter: vec!["public".to_string()],
            query_hash: "test_hash".to_string(),
            index_shard: "shard_tenant1".to_string(),
            allowed_labels: vec!["public".into(), "confidential".into(), "private".into()],
            capabilities: vec![],
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
            query: "test".to_string(),
            labels_filter: vec!["confidential".to_string()],
            query_hash: "test_hash".to_string(),
            index_shard: "shard_tenant1".to_string(),
            allowed_labels: vec!["public".into(), "confidential".into(), "private".into()],
            capabilities: vec![],
        };

        assert!(policy.should_audit(&context));
    }

    fn context(subject_id: &str, labels: &[&str]) -> QueryContext {
        QueryContext {
            tenant: "tenant1".into(),
            subject_id: subject_id.into(),
            query: "reference documents".into(),
            labels_filter: labels.iter().map(|s| (*s).into()).collect(),
            query_hash: "hash".into(),
            index_shard: "shard_tenant1".into(),
            allowed_labels: vec!["public".into(), "private".into(), "confidential".into()],
            capabilities: vec![],
        }
    }

    #[tokio::test]
    async fn public_access_needs_signed_label_scope() {
        let policy = create_test_policy();
        assert!(policy.evaluate(&context("user1", &["public"])).await);
        let mut request = context("user1", &["public"]);
        request.allowed_labels.clear();
        assert!(!policy.evaluate(&request).await);
        request.allowed_labels.push("public".into());
        request.index_shard = "shard_attacker".into();
        assert!(!policy.evaluate(&request).await);
    }

    #[tokio::test]
    async fn missing_or_unknown_label_is_denied() {
        let policy = create_test_policy();
        assert!(!policy.evaluate(&context("user1", &[])).await);
        let mut request = context("user1", &["unknown"]);
        request.allowed_labels.push("unknown".into());
        assert!(!policy.evaluate(&request).await);
    }

    #[tokio::test]
    async fn privileged_subject_does_not_bypass_unimplemented_audit() {
        let policy = create_test_policy();
        let mut request = context("admin_user1", &["confidential"]);
        request.capabilities.push("elevated_privileges".into());
        assert!(!policy.evaluate(&request).await);
    }

    #[tokio::test]
    async fn private_subject_authorization_is_explicit() {
        let mut policy = create_test_policy();
        policy.label_policies.push(LabelPolicy {
            label: "private".into(),
            access_rule: "subject_authorized AND tenant_match".into(),
            description: "Private".into(),
        });
        assert!(!policy.evaluate(&context("user1", &["private"])).await);
        let mut request = context("user1", &["private"]);
        request.capabilities.push("private_access".into());
        assert!(policy.evaluate(&request).await);
    }

    #[tokio::test]
    async fn secret_and_unimplemented_financial_budget_rules_deny() {
        let mut policy = create_test_policy();
        policy.capabilities.insert("financial_access".into(), CapabilityConfig {
            description: "Finance".into(),
            required_for: vec!["financial".into()],
            dp_budget_required: None,
        });
        policy.label_policies.extend([
            LabelPolicy { label: "secret".into(), access_rule: "false".into(), description: "Secret".into() },
            LabelPolicy {
                label: "financial".into(),
                access_rule: "capability:financial_access AND tenant_match AND audit_log".into(),
                description: "Finance".into(),
            },
            LabelPolicy {
                label: "pii".into(),
                access_rule: "dp_budget_available AND tenant_match".into(),
                description: "PII".into(),
            },
        ]);
        let mut request = context("admin_user1", &["secret"]);
        request.allowed_labels.push("secret".into());
        assert!(!policy.evaluate(&request).await);
        request.labels_filter = vec!["financial".into()];
        request.allowed_labels.push("financial".into());
        request.capabilities.push("financial_access".into());
        assert!(!policy.evaluate(&request).await);
        request.labels_filter = vec!["pii".into()];
        request.allowed_labels.push("pii".into());
        assert!(!policy.evaluate(&request).await);
    }

    #[test]
    fn unsupported_policy_predicate_is_rejected_before_start() {
        let mut policy = create_test_policy();
        policy.label_policies.push(LabelPolicy {
            label: "private".into(),
            access_rule: "tenant_match OR true".into(),
            description: "Unsafe".into(),
        });
        assert!(policy.validate_configuration().is_err());
        let mut policy = create_test_policy();
        policy.default_policy = "allow".into();
        assert!(policy.validate_configuration().is_err());
        let policy = create_test_policy();
        assert!(policy.validate_configuration().is_ok());
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