//! Common type definitions for the Provability Fabric Core SDK

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Tenant identifier
pub type TenantId = String;

/// Subject identifier
pub type SubjectId = String;

/// Plan identifier
pub type PlanId = String;

/// Receipt identifier
pub type ReceiptId = String;

/// Certificate identifier
pub type CertificateId = String;

/// Safety case identifier
pub type SafetyCaseId = String;

/// Policy hash
pub type PolicyHash = String;

/// Content hash
pub type ContentHash = String;

/// Signature
pub type Signature = String;

/// Timestamp in seconds since Unix epoch
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Timestamp(pub u64);

impl Timestamp {
    /// Create a timestamp from the current time
    pub fn now() -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or(Duration::from_secs(0));
        Self(now.as_secs())
    }

    /// Create a timestamp from seconds since Unix epoch
    pub fn from_secs(secs: u64) -> Self {
        Self(secs)
    }

    /// Get the timestamp as seconds since Unix epoch
    pub fn as_secs(&self) -> u64 {
        self.0
    }

    /// Get the timestamp as a Duration since Unix epoch
    pub fn as_duration(&self) -> Duration {
        Duration::from_secs(self.0)
    }

    /// Check if the timestamp is in the future
    pub fn is_future(&self) -> bool {
        self.0 > Self::now().0
    }

    /// Check if the timestamp is in the past
    pub fn is_past(&self) -> bool {
        self.0 < Self::now().0
    }

    /// Check if the timestamp has expired (is in the past)
    pub fn is_expired(&self) -> bool {
        self.is_past()
    }

    /// Get the time until this timestamp
    pub fn time_until(&self) -> Duration {
        let now = Self::now().0;
        if self.0 > now {
            Duration::from_secs(self.0 - now)
        } else {
            Duration::from_secs(0)
        }
    }

    /// Get the time since this timestamp
    pub fn time_since(&self) -> Duration {
        let now = Self::now().0;
        if now > self.0 {
            Duration::from_secs(now - self.0)
        } else {
            Duration::from_secs(0)
        }
    }
}

impl From<u64> for Timestamp {
    fn from(secs: u64) -> Self {
        Self(secs)
    }
}

impl From<Timestamp> for u64 {
    fn from(timestamp: Timestamp) -> Self {
        timestamp.0
    }
}

impl From<SystemTime> for Timestamp {
    fn from(time: SystemTime) -> Self {
        time.duration_since(UNIX_EPOCH)
            .map(|d| Self(d.as_secs()))
            .unwrap_or(Self(0))
    }
}

impl From<Timestamp> for SystemTime {
    fn from(timestamp: Timestamp) -> Self {
        UNIX_EPOCH + Duration::from_secs(timestamp.0)
    }
}

/// Risk level enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum RiskLevel {
    /// Negligible risk
    Negligible = 0,
    /// Low risk
    Low = 1,
    /// Medium risk
    Medium = 2,
    /// High risk
    High = 3,
    /// Critical risk
    Critical = 4,
}

impl RiskLevel {
    /// Check if the risk level is acceptable
    pub fn is_acceptable(&self) -> bool {
        matches!(self, Self::Negligible | Self::Low | Self::Medium)
    }

    /// Check if the risk level requires immediate attention
    pub fn requires_attention(&self) -> bool {
        matches!(self, Self::High | Self::Critical)
    }

    /// Get the risk level as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Negligible => "negligible",
            Self::Low => "low",
            Self::Medium => "medium",
            Self::High => "high",
            Self::Critical => "critical",
        }
    }

    /// Get the risk level from a string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "negligible" => Some(Self::Negligible),
            "low" => Some(Self::Low),
            "medium" => Some(Self::Medium),
            "high" => Some(Self::High),
            "critical" => Some(Self::Critical),
            _ => None,
        }
    }
}

impl std::fmt::Display for RiskLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Access level enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AccessLevel {
    /// Read access
    Read = 1,
    /// Write access
    Write = 2,
    /// Delete access
    Delete = 3,
    /// Administrative access
    Admin = 4,
}

impl AccessLevel {
    /// Check if this access level includes read access
    pub fn can_read(&self) -> bool {
        true // All access levels can read
    }

    /// Check if this access level includes write access
    pub fn can_write(&self) -> bool {
        matches!(self, Self::Write | Self::Delete | Self::Admin)
    }

    /// Check if this access level includes delete access
    pub fn can_delete(&self) -> bool {
        matches!(self, Self::Delete | Self::Admin)
    }

    /// Check if this access level includes administrative access
    pub fn is_admin(&self) -> bool {
        matches!(self, Self::Admin)
    }

    /// Get the access level as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Read => "read",
            Self::Write => "write",
            Self::Delete => "delete",
            Self::Admin => "admin",
        }
    }

    /// Get the access level from a string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "read" => Some(Self::Read),
            "write" => Some(Self::Write),
            "delete" => Some(Self::Delete),
            "admin" => Some(Self::Admin),
            _ => None,
        }
    }
}

impl std::fmt::Display for AccessLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Subject type enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SubjectType {
    /// Human user
    User = 1,
    /// Service account
    Service = 2,
    /// AI agent
    Agent = 3,
    /// System process
    System = 4,
}

impl SubjectType {
    /// Check if the subject type is a human user
    pub fn is_human(&self) -> bool {
        matches!(self, Self::User)
    }

    /// Check if the subject type is automated
    pub fn is_automated(&self) -> bool {
        matches!(self, Self::Service | Self::Agent | Self::System)
    }

    /// Check if the subject type requires human oversight
    pub fn requires_oversight(&self) -> bool {
        matches!(self, Self::Agent | Self::System)
    }

    /// Get the subject type as a string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::User => "user",
            Self::Service => "service",
            Self::Agent => "agent",
            Self::System => "system",
        }
    }

    /// Get the subject type from a string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "user" => Some(Self::User),
            "service" => Some(Self::Service),
            "agent" => Some(Self::Agent),
            "system" => Some(Self::System),
            _ => None,
        }
    }
}

impl std::fmt::Display for SubjectType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Capability token
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapabilityToken {
    /// Token identifier
    pub id: String,
    /// Tenant identifier
    pub tenant: TenantId,
    /// Subject identifier
    pub subject: SubjectId,
    /// Granted capabilities
    pub capabilities: Vec<String>,
    /// Token expiration
    pub expires_at: Timestamp,
    /// Token signature
    pub signature: Signature,
    /// Issuer identifier
    pub issuer: String,
    /// Issued at timestamp
    pub issued_at: Timestamp,
}

impl CapabilityToken {
    /// Create a new capability token
    pub fn new(
        id: String,
        tenant: TenantId,
        subject: SubjectId,
        capabilities: Vec<String>,
        expires_at: Timestamp,
        signature: Signature,
        issuer: String,
    ) -> Self {
        Self {
            id,
            tenant,
            subject,
            capabilities,
            expires_at,
            signature,
            issuer,
            issued_at: Timestamp::now(),
        }
    }

    /// Check if the token has expired
    pub fn is_expired(&self) -> bool {
        self.expires_at.is_expired()
    }

    /// Check if the token has a specific capability
    pub fn has_capability(&self, capability: &str) -> bool {
        self.capabilities.iter().any(|c| c == capability)
    }

    /// Check if the token has all required capabilities
    pub fn has_all_capabilities(&self, required: &[String]) -> bool {
        required.iter().all(|c| self.has_capability(c))
    }

    /// Check if the token has any of the required capabilities
    pub fn has_any_capability(&self, required: &[String]) -> bool {
        required.iter().any(|c| self.has_capability(c))
    }

    /// Get the time until token expiration
    pub fn time_until_expiration(&self) -> Duration {
        self.expires_at.time_until()
    }

    /// Get the token age
    pub fn age(&self) -> Duration {
        self.issued_at.time_since()
    }
}

/// Policy rule
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyRule {
    /// Rule identifier
    pub id: String,
    /// Rule name
    pub name: String,
    /// Rule description
    pub description: String,
    /// Rule type
    pub rule_type: String,
    /// Rule conditions
    pub conditions: Vec<PolicyCondition>,
    /// Rule actions
    pub actions: Vec<PolicyAction>,
    /// Rule priority (higher = more important)
    pub priority: u32,
    /// Whether the rule is enabled
    pub enabled: bool,
    /// Rule metadata
    pub metadata: HashMap<String, String>,
}

impl PolicyRule {
    /// Create a new policy rule
    pub fn new(
        id: String,
        name: String,
        description: String,
        rule_type: String,
        conditions: Vec<PolicyCondition>,
        actions: Vec<PolicyAction>,
        priority: u32,
    ) -> Self {
        Self {
            id,
            name,
            description,
            rule_type,
            conditions,
            actions,
            priority,
            enabled: true,
            metadata: HashMap::new(),
        }
    }

    /// Check if the rule is enabled
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Enable the rule
    pub fn enable(&mut self) {
        self.enabled = true;
    }

    /// Disable the rule
    pub fn disable(&mut self) {
        self.enabled = false;
    }

    /// Add metadata to the rule
    pub fn add_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// Get metadata value
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }
}

/// Policy condition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyCondition {
    /// Condition field
    pub field: String,
    /// Condition operator
    pub operator: String,
    /// Condition value
    pub value: String,
    /// Additional parameters
    pub parameters: HashMap<String, String>,
}

impl PolicyCondition {
    /// Create a new policy condition
    pub fn new(field: String, operator: String, value: String) -> Self {
        Self {
            field,
            operator,
            value,
            parameters: HashMap::new(),
        }
    }

    /// Add a parameter to the condition
    pub fn add_parameter(&mut self, key: String, value: String) {
        self.parameters.insert(key, value);
    }

    /// Get a parameter value
    pub fn get_parameter(&self, key: &str) -> Option<&String> {
        self.parameters.get(key)
    }
}

/// Policy action
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PolicyAction {
    /// Action type
    pub action_type: String,
    /// Action parameters
    pub parameters: HashMap<String, String>,
    /// Action severity
    pub severity: String,
}

impl PolicyAction {
    /// Create a new policy action
    pub fn new(action_type: String, severity: String) -> Self {
        Self {
            action_type,
            parameters: HashMap::new(),
            severity,
        }
    }

    /// Add a parameter to the action
    pub fn add_parameter(&mut self, key: String, value: String) {
        self.parameters.insert(key, value);
    }

    /// Get a parameter value
    pub fn get_parameter(&self, key: &str) -> Option<&String> {
        self.parameters.get(key)
    }
}

/// Validation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    /// Whether the validation passed
    pub valid: bool,
    /// Validation reason
    pub reason: String,
    /// Validation errors
    pub errors: Vec<String>,
    /// Validation warnings
    pub warnings: Vec<String>,
    /// Validation score (0.0 to 1.0)
    pub score: f64,
    /// Processing time in milliseconds
    pub processing_time_ms: u64,
}

impl ValidationResult {
    /// Create a successful validation result
    pub fn success(reason: String, score: f64, processing_time_ms: u64) -> Self {
        Self {
            valid: true,
            reason,
            errors: Vec::new(),
            warnings: Vec::new(),
            score,
            processing_time_ms,
        }
    }

    /// Create a failed validation result
    pub fn failure(reason: String, errors: Vec<String>, processing_time_ms: u64) -> Self {
        Self {
            valid: false,
            reason,
            errors,
            warnings: Vec::new(),
            score: 0.0,
            processing_time_ms,
        }
    }

    /// Add a warning to the validation result
    pub fn add_warning(&mut self, warning: String) {
        self.warnings.push(warning);
    }

    /// Add an error to the validation result
    pub fn add_error(&mut self, error: String) {
        self.errors.push(error);
        self.valid = false;
        self.score = 0.0;
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timestamp() {
        let now = Timestamp::now();
        assert!(!now.is_expired());
        assert!(now.is_future() || now.is_past()); // One must be true

        let future = Timestamp::from_secs(now.as_secs() + 3600);
        assert!(future.is_future());
        assert!(!future.is_expired());

        let past = Timestamp::from_secs(now.as_secs() - 3600);
        assert!(past.is_past());
        assert!(past.is_expired());
    }

    #[test]
    fn test_risk_level() {
        assert!(RiskLevel::Low.is_acceptable());
        assert!(!RiskLevel::High.is_acceptable());
        assert!(RiskLevel::Critical.requires_attention());
        assert!(!RiskLevel::Low.requires_attention());

        assert_eq!(RiskLevel::from_str("high"), Some(RiskLevel::High));
        assert_eq!(RiskLevel::from_str("invalid"), None);
    }

    #[test]
    fn test_access_level() {
        assert!(AccessLevel::Read.can_read());
        assert!(!AccessLevel::Read.can_write());
        assert!(AccessLevel::Write.can_write());
        assert!(AccessLevel::Admin.is_admin());

        assert_eq!(AccessLevel::from_str("admin"), Some(AccessLevel::Admin));
        assert_eq!(AccessLevel::from_str("invalid"), None);
    }

    #[test]
    fn test_capability_token() {
        let token = CapabilityToken::new(
            "token_123".to_string(),
            "tenant_001".to_string(),
            "user_001".to_string(),
            vec!["read".to_string(), "write".to_string()],
            Timestamp::from_secs(Timestamp::now().as_secs() + 3600),
            "signature".to_string(),
            "issuer_001".to_string(),
        );

        assert!(!token.is_expired());
        assert!(token.has_capability("read"));
        assert!(token.has_capability("write"));
        assert!(!token.has_capability("delete"));
        assert!(token.has_all_capabilities(&["read".to_string(), "write".to_string()]));
        assert!(token.has_any_capability(&["read".to_string(), "delete".to_string()]));
    }

    #[test]
    fn test_validation_result() {
        let mut result = ValidationResult::success("All good".to_string(), 0.95, 10);
        assert!(result.valid);
        assert_eq!(result.score, 0.95);

        result.add_warning("Minor issue".to_string());
        assert!(result.has_warnings());
        assert!(!result.has_errors());

        result.add_error("Critical error".to_string());
        assert!(result.has_errors());
        assert!(!result.valid);
        assert_eq!(result.score, 0.0);
    }
}
