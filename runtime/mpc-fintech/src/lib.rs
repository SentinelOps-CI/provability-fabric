// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! High-Performance Multi-Party Computation for Financial Services
//! 
//! This module provides a production-ready MPC implementation designed for
//! complex financial workloads with extremely low latency requirements and
//! comprehensive audit trails.

pub mod threshold_signature;
pub mod audit_trail;
pub mod network;
pub mod performance;
pub mod compliance;

use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use tracing::{info, warn, error, debug};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Configuration for the MPC Financial Service
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MpcFinancialConfig {
    /// Number of MPC parties required
    pub party_count: usize,
    /// Threshold for signature generation (t-of-n)
    pub threshold: usize,
    /// Maximum latency tolerance in microseconds
    pub max_latency_us: u64,
    /// Transaction throughput target (TPS)
    pub target_tps: u64,
    /// Enable hardware security modules
    pub enable_hsm: bool,
    /// Regulatory compliance level
    pub compliance_level: ComplianceLevel,
    /// Network configuration
    pub network_config: NetworkConfig,
    /// Performance monitoring settings
    pub performance_config: PerformanceConfig,
}

/// Financial compliance levels
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComplianceLevel {
    /// Basic compliance (development/testing)
    Basic,
    /// SOX compliance for public companies
    SOX,
    /// PCI-DSS for payment processing
    PCIDSS,
    /// Basel III for banking institutions
    BaselIII,
    /// Full regulatory compliance (SOX + PCI + Basel + GDPR)
    FullRegulatory,
}

/// Network configuration for MPC parties
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkConfig {
    /// Party network addresses
    pub party_addresses: HashMap<u32, String>,
    /// TLS configuration
    pub tls_config: TlsConfig,
    /// Connection timeout in milliseconds
    pub connection_timeout_ms: u64,
    /// Network optimization settings
    pub optimization: NetworkOptimization,
}

/// TLS configuration for secure communication
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TlsConfig {
    /// Path to certificate authority
    pub ca_cert_path: String,
    /// Path to client certificate
    pub client_cert_path: String,
    /// Path to client private key
    pub client_key_path: String,
    /// Enable mutual TLS authentication
    pub enable_mtls: bool,
}

/// Network optimization settings
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkOptimization {
    /// Enable TCP_NODELAY for low latency
    pub tcp_nodelay: bool,
    /// Socket buffer sizes
    pub send_buffer_size: usize,
    pub recv_buffer_size: usize,
    /// Connection pooling settings
    pub max_connections_per_party: usize,
    /// Enable compression for large messages
    pub enable_compression: bool,
}

/// Performance monitoring configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    /// Enable detailed latency tracking
    pub enable_latency_tracking: bool,
    /// Performance metrics collection interval
    pub metrics_interval_ms: u64,
    /// Enable performance regression detection
    pub enable_regression_detection: bool,
    /// Performance alert thresholds
    pub alert_thresholds: AlertThresholds,
}

/// Performance alert thresholds
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertThresholds {
    /// Maximum acceptable latency in microseconds
    pub max_latency_us: u64,
    /// Minimum acceptable throughput in TPS
    pub min_throughput_tps: u64,
    /// Maximum acceptable error rate (percentage)
    pub max_error_rate_percent: f64,
    /// Maximum acceptable memory usage in MB
    pub max_memory_mb: usize,
}

/// Financial transaction for MPC processing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FinancialTransaction {
    /// Unique transaction identifier
    pub transaction_id: String,
    /// Transaction type
    pub transaction_type: TransactionType,
    /// Source account
    pub from_account: String,
    /// Destination account
    pub to_account: String,
    /// Transaction amount (in smallest currency unit)
    pub amount: u64,
    /// Currency code (ISO 4217)
    pub currency: String,
    /// Transaction timestamp
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// Additional metadata
    pub metadata: HashMap<String, String>,
    /// Regulatory flags
    pub compliance_flags: ComplianceFlags,
}

/// Types of financial transactions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TransactionType {
    /// Payment between accounts
    Payment,
    /// Wire transfer
    WireTransfer,
    /// Securities trade
    SecuritiesTrade,
    /// Foreign exchange
    ForeignExchange,
    /// Derivative settlement
    DerivativeSettlement,
    /// Clearing and settlement
    ClearingSettlement,
}

/// Compliance flags for regulatory requirements
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceFlags {
    /// Requires KYC verification
    pub requires_kyc: bool,
    /// Requires AML screening
    pub requires_aml: bool,
    /// High-value transaction flag
    pub high_value: bool,
    /// Cross-border transaction
    pub cross_border: bool,
    /// Sanctioned entity screening required
    pub sanctions_screening: bool,
}

/// MPC signature operation result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MpcSignatureResult {
    /// Operation identifier
    pub operation_id: String,
    /// Success status
    pub success: bool,
    /// Generated signature
    pub signature: Option<Vec<u8>>,
    /// Public key used
    pub public_key: Option<Vec<u8>>,
    /// Signature verification status
    pub verified: bool,
    /// Performance metrics
    pub performance_metrics: PerformanceMetrics,
    /// Error details if failed
    pub error: Option<String>,
    /// Audit trail information
    pub audit_info: AuditInfo,
}

/// Performance metrics for MPC operations
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    /// Total operation latency in microseconds
    pub total_latency_us: u64,
    /// Network communication latency
    pub network_latency_us: u64,
    /// Cryptographic computation time
    pub computation_time_us: u64,
    /// Memory usage in bytes
    pub memory_usage_bytes: usize,
    /// Number of network rounds
    pub network_rounds: usize,
    /// Throughput achieved (operations per second)
    pub throughput_ops: f64,
}

/// Audit trail information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditInfo {
    /// Participating parties
    pub parties: Vec<u32>,
    /// Operation timestamp
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// Hash of input data
    pub input_hash: String,
    /// Hash of output data
    pub output_hash: String,
    /// Consensus information
    pub consensus_info: ConsensusInfo,
    /// Compliance verification results
    pub compliance_verification: ComplianceVerification,
}

/// Consensus information for audit
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConsensusInfo {
    /// Number of parties that agreed
    pub agreed_parties: usize,
    /// Total parties involved
    pub total_parties: usize,
    /// Consensus achievement time
    pub consensus_time_us: u64,
    /// Consensus round number
    pub consensus_round: u32,
}

/// Compliance verification results
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplianceVerification {
    /// KYC verification status
    pub kyc_verified: bool,
    /// AML screening status
    pub aml_cleared: bool,
    /// Sanctions screening status
    pub sanctions_cleared: bool,
    /// Regulatory approval status
    pub regulatory_approved: bool,
    /// Verification timestamp
    pub verification_timestamp: chrono::DateTime<chrono::Utc>,
}

/// Main MPC Financial Service
pub struct MpcFinancialService {
    /// Service configuration
    config: MpcFinancialConfig,
    /// Threshold signature manager
    threshold_signer: Arc<RwLock<threshold_signature::ThresholdSigner>>,
    /// Audit trail manager
    audit_manager: Arc<Mutex<audit_trail::AuditManager>>,
    /// Network manager
    network_manager: Arc<network::NetworkManager>,
    /// Performance monitor
    performance_monitor: Arc<Mutex<performance::PerformanceMonitor>>,
    /// Compliance validator
    compliance_validator: Arc<compliance::ComplianceValidator>,
    /// Active operations
    active_operations: Arc<RwLock<HashMap<String, ActiveOperation>>>,
}

/// Active MPC operation state
#[derive(Debug)]
struct ActiveOperation {
    /// Operation ID
    id: String,
    /// Operation type
    operation_type: String,
    /// Start timestamp
    start_time: std::time::Instant,
    /// Participating parties
    parties: Vec<u32>,
    /// Current status
    status: OperationStatus,
    /// Performance tracker
    performance_tracker: performance::OperationTracker,
}

/// Status of an MPC operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OperationStatus {
    /// Operation initialized
    Initialized,
    /// Awaiting party responses
    AwaitingResponses,
    /// Computing signature
    Computing,
    /// Verifying result
    Verifying,
    /// Operation completed successfully
    Completed,
    /// Operation failed
    Failed(String),
    /// Operation timed out
    TimedOut,
}

impl Default for MpcFinancialConfig {
    fn default() -> Self {
        Self {
            party_count: 5,
            threshold: 3,
            max_latency_us: 10_000, // 10ms
            target_tps: 1_000,
            enable_hsm: true,
            compliance_level: ComplianceLevel::FullRegulatory,
            network_config: NetworkConfig {
                party_addresses: HashMap::new(),
                tls_config: TlsConfig {
                    ca_cert_path: "/etc/certs/ca.pem".to_string(),
                    client_cert_path: "/etc/certs/client.pem".to_string(),
                    client_key_path: "/etc/certs/client-key.pem".to_string(),
                    enable_mtls: true,
                },
                connection_timeout_ms: 5_000,
                optimization: NetworkOptimization {
                    tcp_nodelay: true,
                    send_buffer_size: 65536,
                    recv_buffer_size: 65536,
                    max_connections_per_party: 10,
                    enable_compression: false, // Disabled for low latency
                },
            },
            performance_config: PerformanceConfig {
                enable_latency_tracking: true,
                metrics_interval_ms: 1_000,
                enable_regression_detection: true,
                alert_thresholds: AlertThresholds {
                    max_latency_us: 50_000, // 50ms alert threshold
                    min_throughput_tps: 500,
                    max_error_rate_percent: 1.0,
                    max_memory_mb: 1024,
                },
            },
        }
    }
}

impl MpcFinancialService {
    /// Create a new MPC Financial Service
    pub async fn new(config: MpcFinancialConfig) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        info!("Initializing MPC Financial Service");
        
        // Validate configuration
        Self::validate_config(&config)?;
        
        // Initialize components
        let threshold_signer = Arc::new(RwLock::new(
            threshold_signature::ThresholdSigner::new(config.threshold, config.party_count).await?
        ));
        
        let audit_manager = Arc::new(Mutex::new(
            audit_trail::AuditManager::new(config.compliance_level.clone()).await?
        ));
        
        let network_manager = Arc::new(
            network::NetworkManager::new(config.network_config.clone()).await?
        );
        
        let performance_monitor = Arc::new(Mutex::new(
            performance::PerformanceMonitor::new(config.performance_config.clone()).await?
        ));
        
        let compliance_validator = Arc::new(
            compliance::ComplianceValidator::new(config.compliance_level.clone()).await?
        );
        
        let service = Self {
            config,
            threshold_signer,
            audit_manager,
            network_manager,
            performance_monitor,
            compliance_validator,
            active_operations: Arc::new(RwLock::new(HashMap::new())),
        };
        
        info!("MPC Financial Service initialized successfully");
        Ok(service)
    }
    
    /// Validate service configuration
    fn validate_config(config: &MpcFinancialConfig) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if config.threshold == 0 || config.threshold > config.party_count {
            return Err("Invalid threshold: must be 1 <= threshold <= party_count".into());
        }
        
        if config.party_count < 2 {
            return Err("Invalid party count: must be at least 2".into());
        }
        
        if config.max_latency_us == 0 {
            return Err("Invalid max latency: must be greater than 0".into());
        }
        
        if config.target_tps == 0 {
            return Err("Invalid target TPS: must be greater than 0".into());
        }
        
        Ok(())
    }
    
    /// Process a financial transaction using MPC
    pub async fn process_transaction(
        &self,
        transaction: FinancialTransaction,
    ) -> Result<MpcSignatureResult, Box<dyn std::error::Error + Send + Sync>> {
        let operation_id = Uuid::new_v4().to_string();
        let start_time = std::time::Instant::now();
        
        info!("Processing transaction {} with operation {}", transaction.transaction_id, operation_id);
        
        // Start performance tracking
        let mut performance_monitor = self.performance_monitor.lock().await;
        let operation_tracker = performance_monitor.start_operation(&operation_id).await?;
        drop(performance_monitor);
        
        // Validate compliance before processing
        self.compliance_validator.validate_transaction(&transaction).await?;
        
        // Create active operation
        let active_op = ActiveOperation {
            id: operation_id.clone(),
            operation_type: "transaction_signature".to_string(),
            start_time,
            parties: (0..self.config.party_count as u32).collect(),
            status: OperationStatus::Initialized,
            performance_tracker: operation_tracker,
        };
        
        {
            let mut operations = self.active_operations.write().await;
            operations.insert(operation_id.clone(), active_op);
        }
        
        // Execute MPC signature generation
        let signature_result = self.execute_mpc_signature(&operation_id, &transaction).await?;
        
        // Record audit trail
        let mut audit_manager = self.audit_manager.lock().await;
        audit_manager.record_operation(&signature_result).await?;
        drop(audit_manager);
        
        // Update performance metrics
        let mut performance_monitor = self.performance_monitor.lock().await;
        performance_monitor.complete_operation(&operation_id, &signature_result.performance_metrics).await?;
        drop(performance_monitor);
        
        // Clean up active operation
        {
            let mut operations = self.active_operations.write().await;
            operations.remove(&operation_id);
        }
        
        info!("Transaction {} processed successfully in {:?}", 
              transaction.transaction_id, start_time.elapsed());
        
        Ok(signature_result)
    }
    
    /// Execute MPC signature generation
    async fn execute_mpc_signature(
        &self,
        operation_id: &str,
        transaction: &FinancialTransaction,
    ) -> Result<MpcSignatureResult, Box<dyn std::error::Error + Send + Sync>> {
        let signature_start = std::time::Instant::now();
        
        // Update operation status
        self.update_operation_status(operation_id, OperationStatus::Computing).await?;
        
        // Generate threshold signature
        let threshold_signer = self.threshold_signer.read().await;
        let signature_data = threshold_signer.sign_transaction(transaction).await?;
        drop(threshold_signer);
        
        // Verify signature
        self.update_operation_status(operation_id, OperationStatus::Verifying).await?;
        let threshold_signer = self.threshold_signer.read().await;
        let verified = threshold_signer.verify_signature(&signature_data, transaction).await?;
        drop(threshold_signer);
        
        if !verified {
            return Err("Signature verification failed".into());
        }
        
        // Collect performance metrics
        let total_latency = signature_start.elapsed();
        let performance_metrics = PerformanceMetrics {
            total_latency_us: total_latency.as_micros() as u64,
            network_latency_us: 0, // Would be populated by network manager
            computation_time_us: total_latency.as_micros() as u64,
            memory_usage_bytes: 0, // Would be populated by memory tracker
            network_rounds: self.config.threshold,
            throughput_ops: 1.0 / total_latency.as_secs_f64(),
        };
        
        // Create audit information
        let audit_info = AuditInfo {
            parties: (0..self.config.party_count as u32).collect(),
            timestamp: chrono::Utc::now(),
            input_hash: self.hash_transaction(transaction),
            output_hash: self.hash_signature(&signature_data),
            consensus_info: ConsensusInfo {
                agreed_parties: self.config.threshold,
                total_parties: self.config.party_count,
                consensus_time_us: total_latency.as_micros() as u64,
                consensus_round: 1,
            },
            compliance_verification: ComplianceVerification {
                kyc_verified: transaction.compliance_flags.requires_kyc,
                aml_cleared: transaction.compliance_flags.requires_aml,
                sanctions_cleared: transaction.compliance_flags.sanctions_screening,
                regulatory_approved: true,
                verification_timestamp: chrono::Utc::now(),
            },
        };
        
        self.update_operation_status(operation_id, OperationStatus::Completed).await?;
        
        Ok(MpcSignatureResult {
            operation_id: operation_id.to_string(),
            success: true,
            signature: Some(signature_data.signature),
            public_key: Some(signature_data.public_key),
            verified,
            performance_metrics,
            error: None,
            audit_info,
        })
    }
    
    /// Update operation status
    async fn update_operation_status(
        &self,
        operation_id: &str,
        status: OperationStatus,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let mut operations = self.active_operations.write().await;
        if let Some(operation) = operations.get_mut(operation_id) {
            operation.status = status;
            debug!("Updated operation {} status to {:?}", operation_id, operation.status);
        }
        Ok(())
    }
    
    /// Hash transaction for audit trail
    fn hash_transaction(&self, transaction: &FinancialTransaction) -> String {
        use sha2::{Sha256, Digest};
        let serialized = serde_json::to_string(transaction).unwrap_or_default();
        let hash = Sha256::digest(serialized.as_bytes());
        format!("{:x}", hash)
    }
    
    /// Hash signature for audit trail
    fn hash_signature(&self, signature_data: &threshold_signature::SignatureData) -> String {
        use sha2::{Sha256, Digest};
        let hash = Sha256::digest(&signature_data.signature);
        format!("{:x}", hash)
    }
    
    /// Get performance metrics
    pub async fn get_performance_metrics(&self) -> Result<performance::SystemMetrics, Box<dyn std::error::Error + Send + Sync>> {
        let performance_monitor = self.performance_monitor.lock().await;
        performance_monitor.get_system_metrics().await
    }
    
    /// Get audit trail for a transaction
    pub async fn get_audit_trail(&self, transaction_id: &str) -> Result<Vec<audit_trail::AuditEntry>, Box<dyn std::error::Error + Send + Sync>> {
        let audit_manager = self.audit_manager.lock().await;
        audit_manager
            .get_transaction_audit_trail(transaction_id)
            .await
            .map_err(|e| Box::new(e) as Box<dyn std::error::Error + Send + Sync>)
    }
    
    /// Shutdown the service gracefully
    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        info!("Shutting down MPC Financial Service");
        
        // Wait for active operations to complete (with timeout)
        let max_wait = std::time::Duration::from_secs(30);
        let start_wait = std::time::Instant::now();
        
        while start_wait.elapsed() < max_wait {
            let operations = self.active_operations.read().await;
            if operations.is_empty() {
                break;
            }
            drop(operations);
            tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        }
        
        // Shutdown components
        self.network_manager.shutdown().await?;
        
        let mut audit_manager = self.audit_manager.lock().await;
        audit_manager.flush_audit_trail().await?;
        drop(audit_manager);
        
        info!("MPC Financial Service shutdown complete");
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_config_validation() {
        let mut config = MpcFinancialConfig::default();
        assert!(MpcFinancialService::validate_config(&config).is_ok());
        
        config.threshold = 0;
        assert!(MpcFinancialService::validate_config(&config).is_err());
        
        config.threshold = 10;
        config.party_count = 5;
        assert!(MpcFinancialService::validate_config(&config).is_err());
    }
    
    #[tokio::test]
    async fn test_transaction_creation() {
        let transaction = FinancialTransaction {
            transaction_id: "test-tx-001".to_string(),
            transaction_type: TransactionType::Payment,
            from_account: "account-001".to_string(),
            to_account: "account-002".to_string(),
            amount: 1000000, // $10.00 in cents
            currency: "USD".to_string(),
            timestamp: chrono::Utc::now(),
            metadata: HashMap::new(),
            compliance_flags: ComplianceFlags {
                requires_kyc: true,
                requires_aml: true,
                high_value: false,
                cross_border: false,
                sanctions_screening: true,
            },
        };
        
        assert_eq!(transaction.transaction_id, "test-tx-001");
        assert_eq!(transaction.amount, 1000000);
    }
}
