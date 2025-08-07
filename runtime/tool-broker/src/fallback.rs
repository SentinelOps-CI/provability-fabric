use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Fallback response types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FallbackType {
    /// Safe templated response
    SafeTemplate,
    /// Human escalation
    HumanEscalation,
    /// No response (blocked)
    NoResponse,
}

/// Fallback response configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackConfig {
    /// Confidence threshold for fallback (default: 0.6)
    pub confidence_threshold: f64,

    /// Default fallback type
    pub default_fallback: FallbackType,

    /// Template responses for different scenarios
    pub templates: HashMap<String, String>,

    /// Whether to log fallback usage
    pub log_fallback: bool,
}

/// Fallback response
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackResponse {
    /// Type of fallback used
    pub fallback_type: FallbackType,

    /// Response content
    pub content: String,

    /// Reason for fallback
    pub reason: String,

    /// Confidence that triggered fallback
    pub confidence: f64,

    /// Metadata about the fallback
    pub metadata: HashMap<String, String>,
}

/// Fallback handler for low-confidence answers
pub struct FallbackHandler {
    config: FallbackConfig,
}

impl FallbackHandler {
    /// Create new fallback handler
    pub fn new(config: FallbackConfig) -> Self {
        Self { config }
    }

    /// Create default fallback handler
    pub fn default() -> Self {
        let mut templates = HashMap::new();
        templates.insert(
            "low_confidence".to_string(),
            "I don't have enough confidence in my sources to provide a reliable answer. Please try rephrasing your question or contact support for assistance.".to_string(),
        );
        templates.insert(
            "no_sources".to_string(),
            "I couldn't find relevant sources to answer your question. Please try a different query or contact support.".to_string(),
        );
        templates.insert(
            "policy_violation".to_string(),
            "I cannot provide an answer due to policy restrictions. Please contact support for assistance.".to_string(),
        );

        let config = FallbackConfig {
            confidence_threshold: 0.6,
            default_fallback: FallbackType::SafeTemplate,
            templates,
            log_fallback: true,
        };

        Self::new(config)
    }

    /// Check if fallback should be used based on confidence
    pub fn should_use_fallback(&self, confidence: f64) -> bool {
        confidence < self.config.confidence_threshold
    }

    /// Generate fallback response
    pub fn generate_fallback(
        &self,
        confidence: f64,
        reason: &str,
        context: &HashMap<String, String>,
    ) -> FallbackResponse {
        let fallback_type = self.determine_fallback_type(reason, context);
        let content = self.generate_content(&fallback_type, reason, context);

        let mut metadata = HashMap::new();
        metadata.insert("confidence".to_string(), confidence.to_string());
        metadata.insert("reason".to_string(), reason.to_string());
        metadata.insert("fallback_type".to_string(), format!("{:?}", fallback_type));

        if self.config.log_fallback {
            self.log_fallback_usage(confidence, reason, &fallback_type);
        }

        FallbackResponse {
            fallback_type,
            content,
            reason: reason.to_string(),
            confidence,
            metadata,
        }
    }

    /// Determine fallback type based on reason and context
    fn determine_fallback_type(
        &self,
        reason: &str,
        context: &HashMap<String, String>,
    ) -> FallbackType {
        match reason {
            "low_confidence" => FallbackType::SafeTemplate,
            "no_sources" => FallbackType::SafeTemplate,
            "policy_violation" => FallbackType::NoResponse,
            "human_escalation" => FallbackType::HumanEscalation,
            _ => self.config.default_fallback.clone(),
        }
    }

    /// Generate content for fallback response
    fn generate_content(
        &self,
        fallback_type: &FallbackType,
        reason: &str,
        context: &HashMap<String, String>,
    ) -> String {
        match fallback_type {
            FallbackType::SafeTemplate => {
                let template_key = match reason {
                    "low_confidence" => "low_confidence",
                    "no_sources" => "no_sources",
                    "policy_violation" => "policy_violation",
                    _ => "low_confidence",
                };

                self.config
                    .templates
                    .get(template_key)
                    .cloned()
                    .unwrap_or_else(|| {
                        "I cannot provide a reliable answer at this time.".to_string()
                    })
            }

            FallbackType::HumanEscalation => {
                let escalation_id = context
                    .get("escalation_id")
                    .cloned()
                    .unwrap_or_else(|| "ESC-".to_string() + &uuid::Uuid::new_v4().to_string()[..8]);

                format!(
                    "Your request has been escalated to a human agent (ID: {}). You will receive a response within 24 hours.",
                    escalation_id
                )
            }

            FallbackType::NoResponse => {
                "I cannot provide an answer due to policy restrictions.".to_string()
            }
        }
    }

    /// Log fallback usage for monitoring
    fn log_fallback_usage(&self, confidence: f64, reason: &str, fallback_type: &FallbackType) {
        tracing::warn!(
            "Fallback triggered: confidence={:.2}, reason={}, type={:?}",
            confidence,
            reason,
            fallback_type
        );
    }

    /// Get fallback statistics
    pub fn get_fallback_stats(&self) -> FallbackStats {
        // This would typically query a database or metrics system
        FallbackStats {
            total_fallbacks: 0,
            low_confidence_fallbacks: 0,
            policy_violation_fallbacks: 0,
            human_escalations: 0,
            avg_confidence_trigger: 0.0,
        }
    }
}

/// Fallback statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackStats {
    pub total_fallbacks: u64,
    pub low_confidence_fallbacks: u64,
    pub policy_violation_fallbacks: u64,
    pub human_escalations: u64,
    pub avg_confidence_trigger: f64,
}

/// Fallback policy for different scenarios
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackPolicy {
    /// Confidence thresholds for different response types
    pub confidence_thresholds: HashMap<String, f64>,

    /// Fallback types for different scenarios
    pub scenario_fallbacks: HashMap<String, FallbackType>,

    /// Whether to allow human escalation
    pub allow_human_escalation: bool,

    /// Maximum escalation rate (per hour)
    pub max_escalation_rate: u32,
}

impl FallbackPolicy {
    /// Create default fallback policy
    pub fn default() -> Self {
        let mut confidence_thresholds = HashMap::new();
        confidence_thresholds.insert("critical".to_string(), 0.8);
        confidence_thresholds.insert("standard".to_string(), 0.6);
        confidence_thresholds.insert("permissive".to_string(), 0.4);

        let mut scenario_fallbacks = HashMap::new();
        scenario_fallbacks.insert("financial".to_string(), FallbackType::HumanEscalation);
        scenario_fallbacks.insert("medical".to_string(), FallbackType::HumanEscalation);
        scenario_fallbacks.insert("legal".to_string(), FallbackType::NoResponse);
        scenario_fallbacks.insert("general".to_string(), FallbackType::SafeTemplate);

        Self {
            confidence_thresholds,
            scenario_fallbacks,
            allow_human_escalation: true,
            max_escalation_rate: 10,
        }
    }

    /// Get confidence threshold for scenario
    pub fn get_threshold(&self, scenario: &str) -> f64 {
        self.confidence_thresholds
            .get(scenario)
            .cloned()
            .unwrap_or(0.6)
    }

    /// Get fallback type for scenario
    pub fn get_fallback_type(&self, scenario: &str) -> FallbackType {
        self.scenario_fallbacks
            .get(scenario)
            .cloned()
            .unwrap_or(FallbackType::SafeTemplate)
    }

    /// Check if human escalation is allowed
    pub fn can_escalate(&self, current_rate: u32) -> bool {
        self.allow_human_escalation && current_rate < self.max_escalation_rate
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fallback_handler_creation() {
        let handler = FallbackHandler::default();
        assert_eq!(handler.config.confidence_threshold, 0.6);
        assert!(handler.config.templates.contains_key("low_confidence"));
    }

    #[test]
    fn test_should_use_fallback() {
        let handler = FallbackHandler::default();

        assert!(handler.should_use_fallback(0.5));
        assert!(!handler.should_use_fallback(0.7));
        assert!(handler.should_use_fallback(0.6)); // Edge case
    }

    #[test]
    fn test_fallback_response_generation() {
        let handler = FallbackHandler::default();
        let mut context = HashMap::new();
        context.insert("escalation_id".to_string(), "ESC-12345".to_string());

        let response = handler.generate_fallback(0.4, "low_confidence", &context);

        assert_eq!(response.confidence, 0.4);
        assert_eq!(response.reason, "low_confidence");
        assert!(matches!(response.fallback_type, FallbackType::SafeTemplate));
        assert!(!response.content.is_empty());
    }

    #[test]
    fn test_fallback_policy() {
        let policy = FallbackPolicy::default();

        assert_eq!(policy.get_threshold("critical"), 0.8);
        assert_eq!(policy.get_threshold("unknown"), 0.6); // Default

        assert!(matches!(
            policy.get_fallback_type("financial"),
            FallbackType::HumanEscalation
        ));

        assert!(policy.can_escalate(5));
        assert!(!policy.can_escalate(15));
    }
}
