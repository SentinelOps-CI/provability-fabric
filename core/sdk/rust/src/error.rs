//! Error types for the Provability Fabric Core SDK

use thiserror::Error;
use tonic::{Code, Status};

/// Result type for SDK operations
pub type Result<T> = std::result::Result<T, Error>;

/// Error types for the SDK
#[derive(Error, Debug)]
pub enum Error {
    /// gRPC transport error
    #[error("gRPC transport error: {0}")]
    Transport(#[from] tonic::transport::Error),

    /// gRPC status error
    #[error("gRPC status error: {0}")]
    Status(#[from] Status),

    /// Authentication error
    #[error("Authentication error: {0}")]
    Authentication(String),

    /// Authorization error
    #[error("Authorization error: {0}")]
    Authorization(String),

    /// Validation error
    #[error("Validation error: {0}")]
    Validation(String),

    /// Configuration error
    #[error("Configuration error: {0}")]
    Configuration(String),

    /// Serialization error
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    /// Timeout error
    #[error("Operation timed out after {0:?}")]
    Timeout(std::time::Duration),

    /// Connection error
    #[error("Connection error: {0}")]
    Connection(String),

    /// Protocol error
    #[error("Protocol error: {0}")]
    Protocol(String),

    /// Resource not found
    #[error("Resource not found: {0}")]
    NotFound(String),

    /// Resource already exists
    #[error("Resource already exists: {0}")]
    AlreadyExists(String),

    /// Invalid argument
    #[error("Invalid argument: {0}")]
    InvalidArgument(String),

    /// Internal error
    #[error("Internal error: {0}")]
    Internal(String),

    /// Unavailable service
    #[error("Service unavailable: {0}")]
    Unavailable(String),

    /// Rate limit exceeded
    #[error("Rate limit exceeded: {0}")]
    RateLimitExceeded(String),

    /// Quota exceeded
    #[error("Quota exceeded: {0}")]
    QuotaExceeded(String),

    /// Policy violation
    #[error("Policy violation: {0}")]
    PolicyViolation(String),

    /// Safety violation
    #[error("Safety violation: {0}")]
    SafetyViolation(String),

    /// Compliance violation
    #[error("Compliance violation: {0}")]
    ComplianceViolation(String),

    /// Custom error
    #[error("Custom error: {0}")]
    Custom(String),
}

impl Error {
    /// Create a new authentication error
    pub fn auth(message: impl Into<String>) -> Self {
        Self::Authentication(message.into())
    }

    /// Create a new authorization error
    pub fn authz(message: impl Into<String>) -> Self {
        Self::Authorization(message.into())
    }

    /// Create a new validation error
    pub fn validation(message: impl Into<String>) -> Self {
        Self::Validation(message.into())
    }

    /// Create a new configuration error
    pub fn config(message: impl Into<String>) -> Self {
        Self::Configuration(message.into())
    }

    /// Create a new connection error
    pub fn connection(message: impl Into<String>) -> Self {
        Self::Connection(message.into())
    }

    /// Create a new protocol error
    pub fn protocol(message: impl Into<String>) -> Self {
        Self::Protocol(message.into())
    }

    /// Create a new not found error
    pub fn not_found(resource: impl Into<String>) -> Self {
        Self::NotFound(resource.into())
    }

    /// Create a new already exists error
    pub fn already_exists(resource: impl Into<String>) -> Self {
        Self::AlreadyExists(resource.into())
    }

    /// Create a new invalid argument error
    pub fn invalid_argument(arg: impl Into<String>) -> Self {
        Self::InvalidArgument(arg.into())
    }

    /// Create a new internal error
    pub fn internal(message: impl Into<String>) -> Self {
        Self::Internal(message.into())
    }

    /// Create a new unavailable error
    pub fn unavailable(service: impl Into<String>) -> Self {
        Self::Unavailable(service.into())
    }

    /// Create a new rate limit error
    pub fn rate_limit(message: impl Into<String>) -> Self {
        Self::RateLimitExceeded(message.into())
    }

    /// Create a new quota exceeded error
    pub fn quota_exceeded(message: impl Into<String>) -> Self {
        Self::QuotaExceeded(message.into())
    }

    /// Create a new policy violation error
    pub fn policy_violation(message: impl Into<String>) -> Self {
        Self::PolicyViolation(message.into())
    }

    /// Create a new safety violation error
    pub fn safety_violation(message: impl Into<String>) -> Self {
        Self::SafetyViolation(message.into())
    }

    /// Create a new compliance violation error
    pub fn compliance_violation(message: impl Into<String>) -> Self {
        Self::ComplianceViolation(message.into())
    }

    /// Create a new custom error
    pub fn custom(message: impl Into<String>) -> Self {
        Self::Custom(message.into())
    }

    /// Check if the error is retryable
    pub fn is_retryable(&self) -> bool {
        match self {
            Self::Transport(_) => true,
            Self::Status(status) => {
                matches!(
                    status.code(),
                    Code::Unavailable | Code::DeadlineExceeded | Code::ResourceExhausted
                )
            }
            Self::Timeout(_) => true,
            Self::Connection(_) => true,
            Self::Unavailable(_) => true,
            Self::RateLimitExceeded(_) => true,
            Self::QuotaExceeded(_) => true,
            _ => false,
        }
    }

    /// Check if the error is a client error (4xx)
    pub fn is_client_error(&self) -> bool {
        match self {
            Self::Authentication(_) => true,
            Self::Authorization(_) => true,
            Self::Validation(_) => true,
            Self::Configuration(_) => true,
            Self::InvalidArgument(_) => true,
            Self::NotFound(_) => true,
            Self::AlreadyExists(_) => true,
            Self::PolicyViolation(_) => true,
            Self::SafetyViolation(_) => true,
            Self::ComplianceViolation(_) => true,
            _ => false,
        }
    }

    /// Check if the error is a server error (5xx)
    pub fn is_server_error(&self) -> bool {
        match self {
            Self::Internal(_) => true,
            Self::Unavailable(_) => true,
            Self::Transport(_) => true,
            Self::Status(status) => {
                matches!(
                    status.code(),
                    Code::Internal | Code::Unavailable | Code::DataLoss
                )
            }
            _ => false,
        }
    }

    /// Get the error code for metrics/logging
    pub fn error_code(&self) -> &'static str {
        match self {
            Self::Transport(_) => "TRANSPORT_ERROR",
            Self::Status(_) => "GRPC_STATUS_ERROR",
            Self::Authentication(_) => "AUTHENTICATION_ERROR",
            Self::Authorization(_) => "AUTHORIZATION_ERROR",
            Self::Validation(_) => "VALIDATION_ERROR",
            Self::Configuration(_) => "CONFIGURATION_ERROR",
            Self::Serialization(_) => "SERIALIZATION_ERROR",
            Self::Timeout(_) => "TIMEOUT_ERROR",
            Self::Connection(_) => "CONNECTION_ERROR",
            Self::Protocol(_) => "PROTOCOL_ERROR",
            Self::NotFound(_) => "NOT_FOUND_ERROR",
            Self::AlreadyExists(_) => "ALREADY_EXISTS_ERROR",
            Self::InvalidArgument(_) => "INVALID_ARGUMENT_ERROR",
            Self::Internal(_) => "INTERNAL_ERROR",
            Self::Unavailable(_) => "UNAVAILABLE_ERROR",
            Self::RateLimitExceeded(_) => "RATE_LIMIT_ERROR",
            Self::QuotaExceeded(_) => "QUOTA_EXCEEDED_ERROR",
            Self::PolicyViolation(_) => "POLICY_VIOLATION_ERROR",
            Self::SafetyViolation(_) => "SAFETY_VIOLATION_ERROR",
            Self::ComplianceViolation(_) => "COMPLIANCE_VIOLATION_ERROR",
            Self::Custom(_) => "CUSTOM_ERROR",
        }
    }

    /// Get the error severity level
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            Self::Transport(_) => ErrorSeverity::Medium,
            Self::Status(_) => ErrorSeverity::Medium,
            Self::Authentication(_) => ErrorSeverity::High,
            Self::Authorization(_) => ErrorSeverity::High,
            Self::Validation(_) => ErrorSeverity::Medium,
            Self::Configuration(_) => ErrorSeverity::Medium,
            Self::Serialization(_) => ErrorSeverity::Low,
            Self::Timeout(_) => ErrorSeverity::Medium,
            Self::Connection(_) => ErrorSeverity::Medium,
            Self::Protocol(_) => ErrorSeverity::High,
            Self::NotFound(_) => ErrorSeverity::Low,
            Self::AlreadyExists(_) => ErrorSeverity::Low,
            Self::InvalidArgument(_) => ErrorSeverity::Medium,
            Self::Internal(_) => ErrorSeverity::High,
            Self::Unavailable(_) => ErrorSeverity::High,
            Self::RateLimitExceeded(_) => ErrorSeverity::Medium,
            Self::QuotaExceeded(_) => ErrorSeverity::Medium,
            Self::PolicyViolation(_) => ErrorSeverity::Critical,
            Self::SafetyViolation(_) => ErrorSeverity::Critical,
            Self::ComplianceViolation(_) => ErrorSeverity::Critical,
            Self::Custom(_) => ErrorSeverity::Medium,
        }
    }
}

/// Error severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    /// Low severity - informational
    Low = 0,
    /// Medium severity - warning
    Medium = 1,
    /// High severity - error
    High = 2,
    /// Critical severity - system failure
    Critical = 3,
}

impl std::fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Low => write!(f, "LOW"),
            Self::Medium => write!(f, "MEDIUM"),
            Self::High => write!(f, "HIGH"),
            Self::Critical => write!(f, "CRITICAL"),
        }
    }
}

/// Convert tonic status to SDK error
impl From<Status> for Error {
    fn from(status: Status) -> Self {
        match status.code() {
            Code::Ok => Error::Internal("Unexpected OK status".to_string()),
            Code::Cancelled => Error::Internal("Operation cancelled".to_string()),
            Code::Unknown => Error::Internal("Unknown error".to_string()),
            Code::InvalidArgument => Error::InvalidArgument(status.message().to_string()),
            Code::DeadlineExceeded => Error::Timeout(std::time::Duration::from_secs(30)),
            Code::NotFound => Error::NotFound(status.message().to_string()),
            Code::AlreadyExists => Error::AlreadyExists(status.message().to_string()),
            Code::PermissionDenied => Error::Authorization(status.message().to_string()),
            Code::ResourceExhausted => Error::QuotaExceeded(status.message().to_string()),
            Code::FailedPrecondition => Error::Validation(status.message().to_string()),
            Code::Aborted => Error::Internal("Operation aborted".to_string()),
            Code::OutOfRange => Error::InvalidArgument(status.message().to_string()),
            Code::Unimplemented => Error::Protocol(status.message().to_string()),
            Code::Internal => Error::Internal(status.message().to_string()),
            Code::Unavailable => Error::Unavailable(status.message().to_string()),
            Code::DataLoss => Error::Internal("Data loss".to_string()),
            Code::Unauthenticated => Error::Authentication(status.message().to_string()),
            _ => Error::Status(status),
        }
    }
}

/// Convert tonic transport error to SDK error
impl From<tonic::transport::Error> for Error {
    fn from(err: tonic::transport::Error) -> Self {
        if err.to_string().contains("timeout") {
            Error::Timeout(std::time::Duration::from_secs(30))
        } else if err.to_string().contains("connection") {
            Error::Connection(err.to_string())
        } else {
            Error::Transport(err)
        }
    }
}

/// Convert serde error to SDK error
impl From<serde_json::Error> for Error {
    fn from(err: serde_json::Error) -> Self {
        Error::Serialization(err)
    }
}

/// Convert std::io::Error to SDK error
impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        match err.kind() {
            std::io::ErrorKind::TimedOut => Error::Timeout(std::time::Duration::from_secs(30)),
            std::io::ErrorKind::ConnectionRefused => {
                Error::Connection("Connection refused".to_string())
            }
            std::io::ErrorKind::ConnectionReset => {
                Error::Connection("Connection reset".to_string())
            }
            std::io::ErrorKind::ConnectionAborted => {
                Error::Connection("Connection aborted".to_string())
            }
            std::io::ErrorKind::NotConnected => Error::Connection("Not connected".to_string()),
            std::io::ErrorKind::BrokenPipe => Error::Connection("Broken pipe".to_string()),
            std::io::ErrorKind::NotFound => Error::NotFound(err.to_string()),
            std::io::ErrorKind::PermissionDenied => Error::Authorization(err.to_string()),
            std::io::ErrorKind::InvalidInput => Error::InvalidArgument(err.to_string()),
            _ => Error::Internal(err.to_string()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let auth_error = Error::auth("Invalid token");
        assert!(matches!(auth_error, Error::Authentication(_)));
        assert!(auth_error.is_client_error());
        assert!(!auth_error.is_server_error());
        assert!(!auth_error.is_retryable());
        assert_eq!(auth_error.error_code(), "AUTHENTICATION_ERROR");
        assert_eq!(auth_error.severity(), ErrorSeverity::High);

        let internal_error = Error::internal("System failure");
        assert!(matches!(internal_error, Error::Internal(_)));
        assert!(!internal_error.is_client_error());
        assert!(internal_error.is_server_error());
        assert!(!internal_error.is_retryable());
        assert_eq!(internal_error.error_code(), "INTERNAL_ERROR");
        assert_eq!(internal_error.severity(), ErrorSeverity::High);

        let timeout_error = Error::Timeout(std::time::Duration::from_secs(5));
        assert!(timeout_error.is_retryable());
        assert!(!timeout_error.is_client_error());
        assert!(!timeout_error.is_server_error());
        assert_eq!(timeout_error.error_code(), "TIMEOUT_ERROR");
        assert_eq!(timeout_error.severity(), ErrorSeverity::Medium);
    }

    #[test]
    fn test_error_severity() {
        let policy_violation = Error::policy_violation("Critical policy breach");
        assert_eq!(policy_violation.severity(), ErrorSeverity::Critical);

        let validation_error = Error::validation("Invalid input");
        assert_eq!(validation_error.severity(), ErrorSeverity::Medium);

        let not_found = Error::not_found("Resource");
        assert_eq!(not_found.severity(), ErrorSeverity::Low);
    }

    #[test]
    fn test_error_display() {
        let error = Error::custom("Test error");
        let display = format!("{}", error);
        assert!(display.contains("Custom error: Test error"));
    }
}
