use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::fs;

use crate::detectors::DetectionResult;
use crate::EgressRequest;

/// Policy template configuration
#[derive(Debug, Clone, Deserialize)]
pub struct PolicyTemplate {
    pub version: String,
    pub description: String,
    pub global: GlobalSettings,
    pub pii_policies: Vec<PIIPolicy>,
    pub secret_policies: Vec<SecretPolicy>,
    pub memorization_policies: Vec<MemorizationPolicy>,
    pub tenant_policies: Vec<TenantPolicy>,
    pub redaction_templates: HashMap<String, String>,
    pub allowlist: Allowlist,
}

#[derive(Debug, Clone, Deserialize)]
pub struct GlobalSettings {
    pub default_action: String,
    pub max_processing_time_ms: u64,
    pub enable_audit_logging: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct PIIPolicy {
    pub name: String,
    pub description: String,
    pub rules: Vec<DetectionRule>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct SecretPolicy {
    pub name: String,
    pub description: String,
    pub rules: Vec<DetectionRule>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MemorizationPolicy {
    pub name: String,
    pub description: String,
    pub rules: Vec<MemorizationRule>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct DetectionRule {
    pub detector: String,
    pub categories: Vec<String>,
    pub action: String,
    pub confidence_threshold: f64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct MemorizationRule {
    pub detector: String,
    pub similarity_threshold: f64,
    pub action: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct TenantPolicy {
    pub tenant: String,
    pub policy_set: String,
    pub additional_rules: Vec<DetectionRule>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Allowlist {
    pub domains: Vec<String>,
    pub patterns: Vec<String>,
    pub api_keys: Vec<String>,
}

/// Policy evaluation result
#[derive(Debug, Clone, Serialize)]
pub struct PolicyDecision {
    pub allow_egress: bool,
    pub action: String,
    pub reason: String,
    pub applied_rules: Vec<String>,
    pub risk_score: f64,
}

/// Policy engine for evaluating egress requests
pub struct PolicyEngine {
    template: PolicyTemplate,
    policy_hash: String,
}

impl PolicyEngine {
    /// Load policy engine from file
    pub async fn load_from_file(path: &str) -> Result<Self> {
        let content = fs::read_to_string(path)
            .await
            .context("Failed to read policy template file")?;
        
        let template: PolicyTemplate = serde_yaml::from_str(&content)
            .context("Failed to parse policy template YAML")?;
        
        // Compute policy hash for certificate
        let policy_hash = Self::compute_policy_hash(&content);
        
        Ok(Self {
            template,
            policy_hash,
        })
    }

    /// Evaluate egress request against policies
    pub async fn evaluate_egress(
        &self,
        request: &EgressRequest,
        detections: &[DetectionResult],
    ) -> Result<PolicyDecision> {
        let mut decision = PolicyDecision {
            allow_egress: true,
            action: self.template.global.default_action.clone(),
            reason: String::new(),
            applied_rules: Vec::new(),
            risk_score: 0.0,
        };

        // Check allowlist first
        if self.is_allowlisted(&request.text) {
            decision.allow_egress = true;
            decision.action = "allow".to_string();
            decision.reason = "Content is allowlisted".to_string();
            decision.applied_rules.push("allowlist".to_string());
            return Ok(decision);
        }

        // Get tenant-specific policies
        let tenant_policy = self.get_tenant_policy(&request.tenant);

        // Evaluate each detection against policies
        for detection in detections {
            let rule_decision = self.evaluate_detection(detection, tenant_policy.as_ref())?;
            
            if !rule_decision.allow_egress {
                decision.allow_egress = false;
                decision.action = rule_decision.action;
                decision.reason = rule_decision.reason;
            }
            
            decision.applied_rules.extend(rule_decision.applied_rules);
            decision.risk_score = decision.risk_score.max(rule_decision.risk_score);
        }

        // If no blocking rules triggered, apply default action
        if decision.allow_egress && !detections.is_empty() {
            match self.template.global.default_action.as_str() {
                "block" => {
                    decision.allow_egress = false;
                    decision.action = "block".to_string();
                    decision.reason = "Default policy blocks content with detections".to_string();
                }
                "redact" => {
                    decision.action = "redact".to_string();
                    decision.reason = "Default policy redacts detected content".to_string();
                }
                _ => {} // allow
            }
        }

        Ok(decision)
    }

    /// Evaluate a single detection against policies
    fn evaluate_detection(
        &self,
        detection: &DetectionResult,
        tenant_policy: Option<&TenantPolicy>,
    ) -> Result<PolicyDecision> {
        let mut decision = PolicyDecision {
            allow_egress: true,
            action: "allow".to_string(),
            reason: String::new(),
            applied_rules: Vec::new(),
            risk_score: detection.confidence,
        };

        // Check tenant-specific rules first
        if let Some(tenant_pol) = tenant_policy {
            for rule in &tenant_pol.additional_rules {
                if self.rule_matches(rule, detection) {
                    decision = self.apply_rule_action(rule, detection);
                    decision.applied_rules.push(format!("tenant:{}", rule.detector));
                    if !decision.allow_egress {
                        return Ok(decision);
                    }
                }
            }
        }

        // Check global policies by detector type
        match detection.detector_name.as_str() {
            "pii_detector" => {
                for policy in &self.template.pii_policies {
                    for rule in &policy.rules {
                        if self.rule_matches(rule, detection) {
                            decision = self.apply_rule_action(rule, detection);
                            decision.applied_rules.push(format!("pii:{}", policy.name));
                            if !decision.allow_egress {
                                return Ok(decision);
                            }
                        }
                    }
                }
            }
            "secret_detector" => {
                for policy in &self.template.secret_policies {
                    for rule in &policy.rules {
                        if self.rule_matches(rule, detection) {
                            decision = self.apply_rule_action(rule, detection);
                            decision.applied_rules.push(format!("secret:{}", policy.name));
                            if !decision.allow_egress {
                                return Ok(decision);
                            }
                        }
                    }
                }
            }
            "near_dupe_detector" => {
                for policy in &self.template.memorization_policies {
                    for rule in &policy.rules {
                        if detection.confidence >= rule.similarity_threshold {
                            decision.allow_egress = rule.action != "block";
                            decision.action = rule.action.clone();
                            decision.reason = format!("Memorization policy: {}", policy.name);
                            decision.applied_rules.push(format!("memorization:{}", policy.name));
                            if !decision.allow_egress {
                                return Ok(decision);
                            }
                        }
                    }
                }
            }
            _ => {}
        }

        Ok(decision)
    }

    /// Check if a rule matches a detection
    fn rule_matches(&self, rule: &DetectionRule, detection: &DetectionResult) -> bool {
        // Check detector name
        if rule.detector != detection.detector_name && rule.detector != "*" {
            return false;
        }

        // Check confidence threshold
        if detection.confidence < rule.confidence_threshold {
            return false;
        }

        // Check categories if specified
        if !rule.categories.is_empty() {
            let has_matching_category = detection.redactions.iter().any(|redaction| {
                rule.categories.contains(&redaction.category)
            });
            if !has_matching_category {
                return false;
            }
        }

        true
    }

    /// Apply rule action to create decision
    fn apply_rule_action(&self, rule: &DetectionRule, detection: &DetectionResult) -> PolicyDecision {
        PolicyDecision {
            allow_egress: rule.action != "block",
            action: rule.action.clone(),
            reason: format!("Rule {} triggered for {}", rule.action, detection.detector_name),
            applied_rules: vec![rule.detector.clone()],
            risk_score: detection.confidence,
        }
    }

    /// Get tenant-specific policy
    fn get_tenant_policy(&self, tenant: &str) -> Option<&TenantPolicy> {
        self.template.tenant_policies.iter().find(|p| p.tenant == tenant)
    }

    /// Check if content is allowlisted
    fn is_allowlisted(&self, text: &str) -> bool {
        // Check domain allowlist
        for domain in &self.template.allowlist.domains {
            if text.contains(domain) {
                return true;
            }
        }

        // Check pattern allowlist
        for pattern in &self.template.allowlist.patterns {
            if text.contains(pattern) {
                return true;
            }
        }

        false
    }

    /// Get policy hash for certificates
    pub fn get_policy_hash(&self) -> String {
        self.policy_hash.clone()
    }

    /// Get number of loaded policies
    pub async fn policy_count(&self) -> usize {
        self.template.pii_policies.len() + 
        self.template.secret_policies.len() + 
        self.template.memorization_policies.len()
    }

    /// Compute hash of policy content
    fn compute_policy_hash(content: &str) -> String {
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(content.as_bytes());
        format!("{:x}", hasher.finalize())
    }

    /// Get redaction template for category
    pub fn get_redaction_template(&self, category: &str) -> String {
        self.template.redaction_templates
            .get(category)
            .cloned()
            .unwrap_or_else(|| self.template.redaction_templates
                .get("default")
                .cloned()
                .unwrap_or_else(|| "[REDACTED]".to_string())
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::detectors::Redaction;

    #[test]
    fn test_policy_hash_computation() {
        let content = "test policy content";
        let hash = PolicyEngine::compute_policy_hash(content);
        assert_eq!(hash.len(), 64); // SHA-256 hex string
    }

    #[test]
    fn test_rule_matching() {
        let engine = create_test_engine();
        
        let rule = DetectionRule {
            detector: "pii_detector".to_string(),
            categories: vec!["email".to_string()],
            action: "redact".to_string(),
            confidence_threshold: 0.7,
        };

        let detection = DetectionResult {
            detector_name: "pii_detector".to_string(),
            confidence: 0.8,
            redactions: vec![Redaction {
                start: 0,
                end: 5,
                text: "test".to_string(),
                category: "email".to_string(),
            }],
        };

        assert!(engine.rule_matches(&rule, &detection));
    }

    #[test]
    fn test_allowlist_checking() {
        let engine = create_test_engine();
        
        // Test domain allowlist
        assert!(engine.is_allowlisted("Visit example.com for more info"));
        
        // Test pattern allowlist
        assert!(engine.is_allowlisted("Contact test@example.com"));
        
        // Test non-allowlisted content
        assert!(!engine.is_allowlisted("Random content here"));
    }

    fn create_test_engine() -> PolicyEngine {
        let template = PolicyTemplate {
            version: "1.0".to_string(),
            description: "Test template".to_string(),
            global: GlobalSettings {
                default_action: "redact".to_string(),
                max_processing_time_ms: 5000,
                enable_audit_logging: true,
            },
            pii_policies: vec![],
            secret_policies: vec![],
            memorization_policies: vec![],
            tenant_policies: vec![],
            redaction_templates: HashMap::from([
                ("default".to_string(), "[REDACTED]".to_string()),
            ]),
            allowlist: Allowlist {
                domains: vec!["example.com".to_string()],
                patterns: vec!["test@example.com".to_string()],
                api_keys: vec![],
            },
        };

        PolicyEngine {
            template,
            policy_hash: "test_hash".to_string(),
        }
    }
}