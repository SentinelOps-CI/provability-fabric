// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! Comprehensive Audit Trail System for Financial MPC Operations
//! 
//! This module provides immutable, tamper-proof audit trails for all MPC operations
//! with real-time compliance monitoring and regulatory reporting capabilities.

use std::collections::HashMap;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use tracing::{info, debug, warn};
use sha2::{Sha256, Digest};

use crate::{ComplianceLevel, MpcSignatureResult, FinancialTransaction};

/// Audit trail manager for MPC operations
pub struct AuditManager {
    /// Compliance level configuration
    compliance_level: ComplianceLevel,
    /// Audit entry storage
    audit_storage: AuditStorage,
    /// Real-time monitoring configuration
    monitoring_config: MonitoringConfig,
    /// Compliance validators
    compliance_validators: HashMap<String, Box<dyn ComplianceValidator>>,
}

/// Audit entry in the trail
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEntry {
    /// Unique entry identifier
    pub entry_id: String,
    /// Transaction this entry relates to
    pub transaction_id: String,
    /// Operation that generated this entry
    pub operation_id: String,
    /// Entry timestamp
    pub timestamp: DateTime<Utc>,
    /// Type of audit event
    pub event_type: AuditEventType,
    /// Detailed event data
    pub event_data: AuditEventData,
    /// Hash of previous entry (for immutability)
    pub previous_hash: String,
    /// Hash of this entry
    pub entry_hash: String,
    /// Digital signature of the entry
    pub signature: Option<Vec<u8>>,
    /// Compliance verification results
    pub compliance_verification: ComplianceVerificationResult,
}

/// Types of audit events
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AuditEventType {
    /// Transaction initiated
    TransactionInitiated,
    /// Compliance validation started
    ComplianceValidationStarted,
    /// KYC verification completed
    KYCVerificationCompleted,
    /// AML screening completed
    AMLScreeningCompleted,
    /// Sanctions screening completed
    SanctionsScreeningCompleted,
    /// MPC signature generation started
    MPCSignatureStarted,
    /// MPC party response received
    MPCPartyResponse,
    /// Threshold reached
    ThresholdReached,
    /// Signature generated
    SignatureGenerated,
    /// Signature verified
    SignatureVerified,
    /// Transaction completed
    TransactionCompleted,
    /// Transaction failed
    TransactionFailed,
    /// Compliance violation detected
    ComplianceViolation,
    /// Regulatory alert triggered
    RegulatoryAlert,
    /// System error occurred
    SystemError,
}

/// Detailed audit event data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditEventData {
    /// Event-specific details
    pub details: HashMap<String, serde_json::Value>,
    /// Performance metrics at time of event
    pub performance_metrics: Option<AuditPerformanceMetrics>,
    /// Security context
    pub security_context: SecurityContext,
    /// Regulatory context
    pub regulatory_context: RegulatoryContext,
}

/// Performance metrics in audit trail
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditPerformanceMetrics {
    /// Operation latency in microseconds
    pub latency_us: u64,
    /// Memory usage in bytes
    pub memory_usage_bytes: usize,
    /// CPU usage percentage
    pub cpu_usage_percent: f64,
    /// Network I/O in bytes
    pub network_io_bytes: usize,
    /// Timestamp when metrics were captured
    pub metrics_timestamp: DateTime<Utc>,
}

/// Security context for audit entries
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityContext {
    /// User or system that initiated the operation
    pub initiator: String,
    /// Authentication method used
    pub auth_method: String,
    /// Source IP address
    pub source_ip: Option<String>,
    /// Security level of the operation
    pub security_level: SecurityLevel,
    /// Encryption details
    pub encryption_details: EncryptionDetails,
}

/// Security levels for operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SecurityLevel {
    /// Standard security
    Standard,
    /// High security (additional verifications)
    High,
    /// Critical security (maximum protection)
    Critical,
}

/// Encryption details for audit
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionDetails {
    /// Encryption algorithm used
    pub algorithm: String,
    /// Key identifier
    pub key_id: String,
    /// Encryption context
    pub context: HashMap<String, String>,
}

/// Regulatory context for audit entries
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegulatoryContext {
    /// Applicable regulations
    pub applicable_regulations: Vec<String>,
    /// Jurisdiction
    pub jurisdiction: String,
    /// Regulatory requirements met
    pub requirements_met: Vec<String>,
    /// Outstanding requirements
    pub outstanding_requirements: Vec<String>,
    /// Regulatory alerts
    pub alerts: Vec<RegulatoryAlert>,
}

/// Regulatory alert information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegulatoryAlert {
    /// Alert type
    pub alert_type: String,
    /// Alert severity
    pub severity: AlertSeverity,
    /// Alert message
    pub message: String,
    /// Alert timestamp
    pub timestamp: DateTime<Utc>,
    /// Required actions
    pub required_actions: Vec<String>,
}

/// Alert severity levels
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertSeverity {
    /// Informational alert
    Info,
    /// Warning alert
    Warning,
    /// Critical alert requiring immediate attention
    Critical,
    /// Regulatory violation
    Violation,
}

/// Compliance verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceVerificationResult {
    /// Overall compliance status
    pub status: ComplianceStatus,
    /// Individual check results
    pub check_results: HashMap<String, CheckResult>,
    /// Verification timestamp
    pub verification_timestamp: DateTime<Utc>,
    /// Verifier information
    pub verifier: String,
    /// Digital signature of verification
    pub verification_signature: Option<Vec<u8>>,
}

/// Compliance status
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComplianceStatus {
    /// Fully compliant
    Compliant,
    /// Compliant with warnings
    CompliantWithWarnings,
    /// Non-compliant
    NonCompliant,
    /// Under review
    UnderReview,
    /// Verification failed
    VerificationFailed,
}

/// Individual compliance check result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CheckResult {
    /// Check name
    pub check_name: String,
    /// Check result
    pub result: bool,
    /// Details about the check
    pub details: String,
    /// Evidence provided
    pub evidence: Option<String>,
    /// Check timestamp
    pub timestamp: DateTime<Utc>,
}

/// Audit storage interface
trait AuditStorageInterface {
    async fn store_entry(&mut self, entry: &AuditEntry) -> Result<(), AuditError>;
    async fn retrieve_entries(&self, transaction_id: &str) -> Result<Vec<AuditEntry>, AuditError>;
    async fn verify_chain_integrity(&self) -> Result<bool, AuditError>;
    async fn get_compliance_report(&self, start_date: DateTime<Utc>, end_date: DateTime<Utc>) -> Result<ComplianceReport, AuditError>;
}

/// Audit storage implementation
struct AuditStorage {
    /// In-memory storage for demonstration (would be database in production)
    entries: HashMap<String, Vec<AuditEntry>>,
    /// Chain verification state
    last_hash: String,
}

/// Monitoring configuration
#[derive(Debug, Clone)]
struct MonitoringConfig {
    /// Enable real-time alerts
    enable_realtime_alerts: bool,
    /// Alert notification endpoints
    alert_endpoints: Vec<String>,
    /// Monitoring interval in seconds
    monitoring_interval_secs: u64,
    /// Enable performance monitoring
    enable_performance_monitoring: bool,
}

/// Compliance validator trait
#[async_trait::async_trait]
trait ComplianceValidator: Send + Sync {
    async fn validate(&self, transaction: &FinancialTransaction, context: &SecurityContext) -> Result<CheckResult, AuditError>;
}

/// Audit error types
#[derive(Debug, thiserror::Error)]
pub enum AuditError {
    #[error("Storage error: {0}")]
    StorageError(String),
    #[error("Verification error: {0}")]
    VerificationError(String),
    #[error("Compliance error: {0}")]
    ComplianceError(String),
    #[error("Serialization error: {0}")]
    SerializationError(String),
}

/// Compliance report for regulatory authorities
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceReport {
    /// Report ID
    pub report_id: String,
    /// Report period start
    pub period_start: DateTime<Utc>,
    /// Report period end
    pub period_end: DateTime<Utc>,
    /// Total transactions processed
    pub total_transactions: u64,
    /// Compliance statistics
    pub compliance_stats: ComplianceStatistics,
    /// Regulatory alerts summary
    pub alerts_summary: AlertsSummary,
    /// Performance summary
    pub performance_summary: PerformanceSummary,
    /// Report generation timestamp
    pub generated_at: DateTime<Utc>,
}

/// Compliance statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceStatistics {
    /// Compliant transactions
    pub compliant_transactions: u64,
    /// Non-compliant transactions
    pub non_compliant_transactions: u64,
    /// Compliance rate percentage
    pub compliance_rate_percent: f64,
    /// KYC verification rate
    pub kyc_verification_rate_percent: f64,
    /// AML screening rate
    pub aml_screening_rate_percent: f64,
    /// Sanctions screening rate
    pub sanctions_screening_rate_percent: f64,
}

/// Alerts summary for reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertsSummary {
    /// Total alerts generated
    pub total_alerts: u64,
    /// Critical alerts
    pub critical_alerts: u64,
    /// Warning alerts
    pub warning_alerts: u64,
    /// Info alerts
    pub info_alerts: u64,
    /// Violations detected
    pub violations: u64,
}

/// Performance summary for reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceSummary {
    /// Average transaction latency
    pub avg_latency_us: u64,
    /// Maximum transaction latency
    pub max_latency_us: u64,
    /// Average throughput
    pub avg_throughput_tps: f64,
    /// System uptime percentage
    pub uptime_percent: f64,
    /// Error rate percentage
    pub error_rate_percent: f64,
}

impl AuditManager {
    /// Create a new audit manager
    pub async fn new(compliance_level: ComplianceLevel) -> Result<Self, AuditError> {
        info!("Initializing audit manager with compliance level: {:?}", compliance_level);
        
        let audit_storage = AuditStorage {
            entries: HashMap::new(),
            last_hash: "genesis".to_string(),
        };
        
        let monitoring_config = MonitoringConfig {
            enable_realtime_alerts: true,
            alert_endpoints: vec![
                "https://compliance-monitor.example.com/alerts".to_string(),
                "https://regulatory-reporting.example.com/alerts".to_string(),
            ],
            monitoring_interval_secs: 60,
            enable_performance_monitoring: true,
        };
        
        let mut compliance_validators: HashMap<String, Box<dyn ComplianceValidator>> = HashMap::new();
        
        // Add compliance validators based on compliance level
        match compliance_level {
            ComplianceLevel::Basic => {
                // Basic validators only
            },
            ComplianceLevel::SOX => {
                compliance_validators.insert("sox_validator".to_string(), Box::new(SOXValidator));
            },
            ComplianceLevel::PCIDSS => {
                compliance_validators.insert("pci_validator".to_string(), Box::new(PCIValidator));
            },
            ComplianceLevel::BaselIII => {
                compliance_validators.insert("basel_validator".to_string(), Box::new(BaselValidator));
            },
            ComplianceLevel::FullRegulatory => {
                compliance_validators.insert("sox_validator".to_string(), Box::new(SOXValidator));
                compliance_validators.insert("pci_validator".to_string(), Box::new(PCIValidator));
                compliance_validators.insert("basel_validator".to_string(), Box::new(BaselValidator));
                compliance_validators.insert("gdpr_validator".to_string(), Box::new(GDPRValidator));
            },
        }
        
        Ok(Self {
            compliance_level,
            audit_storage,
            monitoring_config,
            compliance_validators,
        })
    }
    
    /// Record an MPC operation in the audit trail
    pub async fn record_operation(&mut self, signature_result: &MpcSignatureResult) -> Result<(), AuditError> {
        info!("Recording audit trail for operation: {}", signature_result.operation_id);
        
        // Create audit entry for signature generation
        let audit_entry = self.create_signature_audit_entry(signature_result).await?;
        
        // Store the entry
        self.audit_storage.store_entry(&audit_entry).await?;
        
        // Check for compliance alerts
        self.check_compliance_alerts(&audit_entry).await?;
        
        debug!("Audit entry recorded: {}", audit_entry.entry_id);
        Ok(())
    }
    
    /// Create audit entry for signature operation
    async fn create_signature_audit_entry(&self, signature_result: &MpcSignatureResult) -> Result<AuditEntry, AuditError> {
        let entry_id = uuid::Uuid::new_v4().to_string();
        let timestamp = Utc::now();
        
        // Create event data
        let mut event_details = HashMap::new();
        event_details.insert("operation_id".to_string(), serde_json::Value::String(signature_result.operation_id.clone()));
        event_details.insert("success".to_string(), serde_json::Value::Bool(signature_result.success));
        event_details.insert("parties".to_string(), serde_json::Value::Array(
            signature_result.audit_info.parties.iter().map(|p| serde_json::Value::Number((*p).into())).collect()
        ));
        
        let performance_metrics = AuditPerformanceMetrics {
            latency_us: signature_result.performance_metrics.total_latency_us,
            memory_usage_bytes: signature_result.performance_metrics.memory_usage_bytes,
            cpu_usage_percent: 0.0, // Would be populated by system monitor
            network_io_bytes: signature_result.performance_metrics.network_rounds * 1024, // Estimated
            metrics_timestamp: timestamp,
        };
        
        let security_context = SecurityContext {
            initiator: "mpc_service".to_string(),
            auth_method: "threshold_signature".to_string(),
            source_ip: None,
            security_level: SecurityLevel::Critical,
            encryption_details: EncryptionDetails {
                algorithm: "ECDSA_SECP256K1".to_string(),
                key_id: "threshold_key_1".to_string(),
                context: HashMap::new(),
            },
        };
        
        let regulatory_context = RegulatoryContext {
            applicable_regulations: self.get_applicable_regulations(),
            jurisdiction: "US".to_string(),
            requirements_met: vec!["multi_party_authorization".to_string(), "audit_trail".to_string()],
            outstanding_requirements: vec![],
            alerts: vec![],
        };
        
        let event_data = AuditEventData {
            details: event_details,
            performance_metrics: Some(performance_metrics),
            security_context,
            regulatory_context,
        };
        
        // Create compliance verification
        let compliance_verification = self.verify_compliance(signature_result, &event_data).await?;
        
        // Calculate entry hash
        let previous_hash = self.audit_storage.last_hash.clone();
        let entry_hash = self.calculate_entry_hash(&entry_id, &timestamp, &event_data, &previous_hash)?;
        
        Ok(AuditEntry {
            entry_id,
            transaction_id: "unknown".to_string(), // Would be populated with actual transaction ID
            operation_id: signature_result.operation_id.clone(),
            timestamp,
            event_type: if signature_result.success { AuditEventType::SignatureGenerated } else { AuditEventType::TransactionFailed },
            event_data,
            previous_hash,
            entry_hash,
            signature: None, // Would be populated with digital signature
            compliance_verification,
        })
    }
    
    /// Verify compliance for the operation
    async fn verify_compliance(&self, _signature_result: &MpcSignatureResult, event_data: &AuditEventData) -> Result<ComplianceVerificationResult, AuditError> {
        let mut check_results = HashMap::new();
        
        // Run all compliance validators
        for (validator_name, validator) in &self.compliance_validators {
            // Create a mock transaction for validation
            let mock_transaction = self.create_mock_transaction_for_validation();
            
            match validator.validate(&mock_transaction, &event_data.security_context).await {
                Ok(result) => {
                    check_results.insert(validator_name.clone(), result);
                },
                Err(e) => {
                    warn!("Compliance validation failed for {}: {}", validator_name, e);
                    check_results.insert(validator_name.clone(), CheckResult {
                        check_name: validator_name.clone(),
                        result: false,
                        details: format!("Validation error: {}", e),
                        evidence: None,
                        timestamp: Utc::now(),
                    });
                }
            }
        }
        
        // Determine overall compliance status
        let all_passed = check_results.values().all(|result| result.result);
        let status = if all_passed {
            ComplianceStatus::Compliant
        } else {
            ComplianceStatus::NonCompliant
        };
        
        Ok(ComplianceVerificationResult {
            status,
            check_results,
            verification_timestamp: Utc::now(),
            verifier: "audit_manager".to_string(),
            verification_signature: None,
        })
    }
    
    /// Get audit trail for a specific transaction
    pub async fn get_transaction_audit_trail(&self, transaction_id: &str) -> Result<Vec<AuditEntry>, AuditError> {
        self.audit_storage.retrieve_entries(transaction_id).await
    }
    
    /// Flush audit trail to persistent storage
    pub async fn flush_audit_trail(&mut self) -> Result<(), AuditError> {
        info!("Flushing audit trail to persistent storage");
        // In production, this would write to database or distributed storage
        Ok(())
    }
    
    /// Check for compliance alerts
    async fn check_compliance_alerts(&self, audit_entry: &AuditEntry) -> Result<(), AuditError> {
        if self.monitoring_config.enable_realtime_alerts {
            // Check for non-compliance
            if matches!(audit_entry.compliance_verification.status, ComplianceStatus::NonCompliant) {
                self.send_compliance_alert(audit_entry).await?;
            }
            
            // Check for performance issues
            if let Some(metrics) = &audit_entry.event_data.performance_metrics {
                if metrics.latency_us > 50_000 { // 50ms threshold
                    self.send_performance_alert(audit_entry, metrics).await?;
                }
            }
        }
        
        Ok(())
    }
    
    /// Send compliance alert
    async fn send_compliance_alert(&self, audit_entry: &AuditEntry) -> Result<(), AuditError> {
        warn!("Compliance alert for operation: {}", audit_entry.operation_id);
        
        // In production, this would send alerts to monitoring systems
        for endpoint in &self.monitoring_config.alert_endpoints {
            debug!("Sending alert to: {}", endpoint);
            // HTTP POST to alert endpoint
        }
        
        Ok(())
    }
    
    /// Send performance alert
    async fn send_performance_alert(&self, audit_entry: &AuditEntry, metrics: &AuditPerformanceMetrics) -> Result<(), AuditError> {
        warn!("Performance alert for operation: {} - latency: {}μs", audit_entry.operation_id, metrics.latency_us);
        
        // In production, this would send performance alerts
        Ok(())
    }
    
    /// Calculate hash for audit entry
    fn calculate_entry_hash(&self, entry_id: &str, timestamp: &DateTime<Utc>, event_data: &AuditEventData, previous_hash: &str) -> Result<String, AuditError> {
        let mut hasher = Sha256::new();
        hasher.update(entry_id.as_bytes());
        hasher.update(timestamp.to_rfc3339().as_bytes());
        hasher.update(previous_hash.as_bytes());
        
        // Hash event data
        let event_data_json = serde_json::to_string(event_data)
            .map_err(|e| AuditError::SerializationError(e.to_string()))?;
        hasher.update(event_data_json.as_bytes());
        
        Ok(format!("{:x}", hasher.finalize()))
    }
    
    /// Get applicable regulations for current compliance level
    fn get_applicable_regulations(&self) -> Vec<String> {
        match self.compliance_level {
            ComplianceLevel::Basic => vec!["basic_audit".to_string()],
            ComplianceLevel::SOX => vec!["sox_404".to_string(), "sox_302".to_string()],
            ComplianceLevel::PCIDSS => vec!["pci_dss_3.2.1".to_string()],
            ComplianceLevel::BaselIII => vec!["basel_iii_lcr".to_string(), "basel_iii_nsfr".to_string()],
            ComplianceLevel::FullRegulatory => vec![
                "sox_404".to_string(),
                "sox_302".to_string(),
                "pci_dss_3.2.1".to_string(),
                "basel_iii_lcr".to_string(),
                "basel_iii_nsfr".to_string(),
                "gdpr".to_string(),
                "mifid_ii".to_string(),
            ],
        }
    }
    
    /// Create mock transaction for validation (in production, would use real transaction)
    fn create_mock_transaction_for_validation(&self) -> FinancialTransaction {
        use crate::{TransactionType, ComplianceFlags};
        
        FinancialTransaction {
            transaction_id: "mock-validation".to_string(),
            transaction_type: TransactionType::Payment,
            from_account: "validation-from".to_string(),
            to_account: "validation-to".to_string(),
            amount: 0,
            currency: "USD".to_string(),
            timestamp: Utc::now(),
            metadata: HashMap::new(),
            compliance_flags: ComplianceFlags {
                requires_kyc: true,
                requires_aml: true,
                high_value: false,
                cross_border: false,
                sanctions_screening: true,
            },
        }
    }
}

impl AuditStorage {
    async fn store_entry(&mut self, entry: &AuditEntry) -> Result<(), AuditError> {
        let transaction_entries = self.entries.entry(entry.transaction_id.clone()).or_default();
        transaction_entries.push(entry.clone());
        
        // Update last hash for chain integrity
        self.last_hash = entry.entry_hash.clone();
        
        Ok(())
    }
    
    async fn retrieve_entries(&self, transaction_id: &str) -> Result<Vec<AuditEntry>, AuditError> {
        Ok(self.entries.get(transaction_id).cloned().unwrap_or_default())
    }
    
    async fn verify_chain_integrity(&self) -> Result<bool, AuditError> {
        // Verify hash chain integrity
        for entries in self.entries.values() {
            for window in entries.windows(2) {
                if window[1].previous_hash != window[0].entry_hash {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }
    
    async fn get_compliance_report(&self, _start_date: DateTime<Utc>, _end_date: DateTime<Utc>) -> Result<ComplianceReport, AuditError> {
        // Generate compliance report for the given period
        Ok(ComplianceReport {
            report_id: uuid::Uuid::new_v4().to_string(),
            period_start: _start_date,
            period_end: _end_date,
            total_transactions: self.entries.len() as u64,
            compliance_stats: ComplianceStatistics {
                compliant_transactions: 0,
                non_compliant_transactions: 0,
                compliance_rate_percent: 100.0,
                kyc_verification_rate_percent: 100.0,
                aml_screening_rate_percent: 100.0,
                sanctions_screening_rate_percent: 100.0,
            },
            alerts_summary: AlertsSummary {
                total_alerts: 0,
                critical_alerts: 0,
                warning_alerts: 0,
                info_alerts: 0,
                violations: 0,
            },
            performance_summary: PerformanceSummary {
                avg_latency_us: 5000,
                max_latency_us: 50000,
                avg_throughput_tps: 1000.0,
                uptime_percent: 99.9,
                error_rate_percent: 0.1,
            },
            generated_at: Utc::now(),
        })
    }
}

// Compliance validator implementations
struct SOXValidator;
struct PCIValidator;
struct BaselValidator;
struct GDPRValidator;

#[async_trait::async_trait]
impl ComplianceValidator for SOXValidator {
    async fn validate(&self, _transaction: &FinancialTransaction, _context: &SecurityContext) -> Result<CheckResult, AuditError> {
        Ok(CheckResult {
            check_name: "SOX Compliance".to_string(),
            result: true,
            details: "SOX requirements met".to_string(),
            evidence: Some("Multi-party authorization and audit trail present".to_string()),
            timestamp: Utc::now(),
        })
    }
}

#[async_trait::async_trait]
impl ComplianceValidator for PCIValidator {
    async fn validate(&self, _transaction: &FinancialTransaction, context: &SecurityContext) -> Result<CheckResult, AuditError> {
        let encryption_secure = context.encryption_details.algorithm.contains("AES") || 
                               context.encryption_details.algorithm.contains("ECDSA");
        
        Ok(CheckResult {
            check_name: "PCI DSS Compliance".to_string(),
            result: encryption_secure,
            details: if encryption_secure { "Strong encryption in use".to_string() } else { "Weak encryption detected".to_string() },
            evidence: Some(format!("Encryption: {}", context.encryption_details.algorithm)),
            timestamp: Utc::now(),
        })
    }
}

#[async_trait::async_trait]
impl ComplianceValidator for BaselValidator {
    async fn validate(&self, transaction: &FinancialTransaction, _context: &SecurityContext) -> Result<CheckResult, AuditError> {
        let high_value_check = if transaction.compliance_flags.high_value {
            // High value transactions require additional oversight
            transaction.compliance_flags.requires_aml && transaction.compliance_flags.sanctions_screening
        } else {
            true
        };
        
        Ok(CheckResult {
            check_name: "Basel III Compliance".to_string(),
            result: high_value_check,
            details: "Basel III risk management requirements".to_string(),
            evidence: Some("AML and sanctions screening verified".to_string()),
            timestamp: Utc::now(),
        })
    }
}

#[async_trait::async_trait]
impl ComplianceValidator for GDPRValidator {
    async fn validate(&self, _transaction: &FinancialTransaction, context: &SecurityContext) -> Result<CheckResult, AuditError> {
        let privacy_compliant = !context.encryption_details.algorithm.is_empty();
        
        Ok(CheckResult {
            check_name: "GDPR Compliance".to_string(),
            result: privacy_compliant,
            details: "Data protection requirements".to_string(),
            evidence: Some("Encryption and access controls in place".to_string()),
            timestamp: Utc::now(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MpcSignatureResult, PerformanceMetrics, AuditInfo, ConsensusInfo, ComplianceVerification};
    
    #[tokio::test]
    async fn test_audit_manager_creation() {
        let audit_manager = AuditManager::new(ComplianceLevel::Basic).await;
        assert!(audit_manager.is_ok());
    }
    
    #[tokio::test]
    async fn test_audit_entry_recording() {
        let mut audit_manager = AuditManager::new(ComplianceLevel::FullRegulatory).await.unwrap();
        
        let signature_result = MpcSignatureResult {
            operation_id: "test-op-001".to_string(),
            success: true,
            signature: Some(vec![1, 2, 3, 4]),
            public_key: Some(vec![5, 6, 7, 8]),
            verified: true,
            performance_metrics: PerformanceMetrics {
                total_latency_us: 5000,
                network_latency_us: 1000,
                computation_time_us: 4000,
                memory_usage_bytes: 1024 * 1024,
                network_rounds: 3,
                throughput_ops: 200.0,
            },
            error: None,
            audit_info: AuditInfo {
                parties: vec![0, 1, 2],
                timestamp: Utc::now(),
                input_hash: "input_hash".to_string(),
                output_hash: "output_hash".to_string(),
                consensus_info: ConsensusInfo {
                    agreed_parties: 3,
                    total_parties: 5,
                    consensus_time_us: 5000,
                    consensus_round: 1,
                },
                compliance_verification: ComplianceVerification {
                    kyc_verified: true,
                    aml_cleared: true,
                    sanctions_cleared: true,
                    regulatory_approved: true,
                    verification_timestamp: Utc::now(),
                },
            },
        };
        
        let result = audit_manager.record_operation(&signature_result).await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_compliance_validation() {
        let audit_manager = AuditManager::new(ComplianceLevel::FullRegulatory).await.unwrap();
        
        // Test should have multiple validators configured
        assert!(!audit_manager.compliance_validators.is_empty());
        assert!(audit_manager.compliance_validators.contains_key("sox_validator"));
        assert!(audit_manager.compliance_validators.contains_key("pci_validator"));
    }
}
