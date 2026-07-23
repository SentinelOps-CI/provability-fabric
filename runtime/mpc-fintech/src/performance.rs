// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

//! Performance Monitoring and Optimization for MPC Financial Operations
//! 
//! This module provides real-time performance monitoring, regression detection,
//! and optimization recommendations for financial MPC workloads.

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use tokio::sync::Mutex;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use tracing::{info, debug, warn, error};

use crate::{PerformanceConfig, PerformanceMetrics};

/// Performance monitor for MPC operations
pub struct PerformanceMonitor {
    /// Configuration
    config: PerformanceConfig,
    /// Operation trackers
    active_operations: HashMap<String, OperationTracker>,
    /// Historical performance data
    historical_data: VecDeque<PerformanceSnapshot>,
    /// Performance alerts
    alerts: Vec<PerformanceAlert>,
    /// System metrics
    system_metrics: SystemMetrics,
}

/// Individual operation performance tracker
#[derive(Debug, Clone)]
pub struct OperationTracker {
    /// Operation ID
    pub operation_id: String,
    /// Start timestamp
    pub start_time: std::time::Instant,
    /// Operation type
    pub operation_type: String,
    /// Performance checkpoints
    pub checkpoints: Vec<PerformanceCheckpoint>,
    /// Resource usage tracking
    pub resource_usage: ResourceUsage,
}

/// Performance checkpoint during operation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceCheckpoint {
    /// Checkpoint name
    pub name: String,
    /// Timestamp
    pub timestamp: DateTime<Utc>,
    /// Elapsed time since operation start
    pub elapsed_us: u64,
    /// Memory usage at checkpoint
    pub memory_usage_bytes: usize,
    /// Additional metrics
    pub metrics: HashMap<String, f64>,
}

/// Resource usage tracking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUsage {
    /// Peak memory usage
    pub peak_memory_bytes: usize,
    /// Total CPU time consumed
    pub cpu_time_us: u64,
    /// Network I/O bytes
    pub network_io_bytes: usize,
    /// Disk I/O operations
    pub disk_io_ops: u64,
    /// Thread count
    pub thread_count: usize,
}

/// Performance snapshot for trend analysis
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceSnapshot {
    /// Snapshot timestamp
    pub timestamp: DateTime<Utc>,
    /// System performance metrics
    pub system_metrics: SystemMetrics,
    /// Operation statistics
    pub operation_stats: OperationStatistics,
    /// Alert summary
    pub alert_summary: AlertSummary,
}

/// System-wide performance metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemMetrics {
    /// Overall system latency percentiles
    pub latency_percentiles: LatencyPercentiles,
    /// Throughput metrics
    pub throughput_metrics: ThroughputMetrics,
    /// Resource utilization
    pub resource_utilization: ResourceUtilization,
    /// Error rates
    pub error_rates: ErrorRates,
    /// Timestamp
    pub timestamp: DateTime<Utc>,
}

/// Latency percentile measurements
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LatencyPercentiles {
    /// 50th percentile (median)
    pub p50_us: u64,
    /// 95th percentile
    pub p95_us: u64,
    /// 99th percentile
    pub p99_us: u64,
    /// 99.9th percentile
    pub p999_us: u64,
    /// Maximum latency observed
    pub max_us: u64,
}

/// Throughput measurements
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ThroughputMetrics {
    /// Transactions per second
    pub tps: f64,
    /// Operations per second
    pub ops: f64,
    /// Signatures per second
    pub sps: f64,
    /// Peak throughput achieved
    pub peak_tps: f64,
}

/// Resource utilization metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUtilization {
    /// CPU utilization percentage
    pub cpu_percent: f64,
    /// Memory utilization percentage
    pub memory_percent: f64,
    /// Network utilization percentage
    pub network_percent: f64,
    /// Disk utilization percentage
    pub disk_percent: f64,
}

/// Error rate metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorRates {
    /// Overall error rate percentage
    pub overall_percent: f64,
    /// Network error rate
    pub network_percent: f64,
    /// Computation error rate
    pub computation_percent: f64,
    /// Timeout error rate
    pub timeout_percent: f64,
}

/// Operation statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OperationStatistics {
    /// Total operations completed
    pub total_operations: u64,
    /// Successful operations
    pub successful_operations: u64,
    /// Failed operations
    pub failed_operations: u64,
    /// Average operation time
    pub avg_operation_time_us: u64,
    /// Operations by type
    pub operations_by_type: HashMap<String, u64>,
}

/// Alert summary
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertSummary {
    /// Total alerts generated
    pub total_alerts: u64,
    /// Critical alerts
    pub critical_alerts: u64,
    /// Warning alerts
    pub warning_alerts: u64,
    /// Performance regression alerts
    pub regression_alerts: u64,
}

/// Performance alert
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceAlert {
    /// Alert ID
    pub alert_id: String,
    /// Alert severity
    pub severity: AlertSeverity,
    /// Alert type
    pub alert_type: AlertType,
    /// Alert message
    pub message: String,
    /// Timestamp
    pub timestamp: DateTime<Utc>,
    /// Affected metrics
    pub affected_metrics: Vec<String>,
    /// Recommended actions
    pub recommended_actions: Vec<String>,
}

/// Alert severity levels
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertSeverity {
    /// Information only
    Info,
    /// Warning - attention needed
    Warning,
    /// Critical - immediate action required
    Critical,
}

/// Alert types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertType {
    /// Latency threshold exceeded
    LatencyThreshold,
    /// Throughput below target
    ThroughputBelow,
    /// Error rate too high
    ErrorRateHigh,
    /// Resource utilization high
    ResourceUtilizationHigh,
    /// Performance regression detected
    PerformanceRegression,
    /// System overload
    SystemOverload,
}

impl PerformanceMonitor {
    /// Create a new performance monitor
    pub async fn new(config: PerformanceConfig) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        info!("Initializing performance monitor");
        
        Ok(Self {
            config,
            active_operations: HashMap::new(),
            historical_data: VecDeque::with_capacity(1000), // Keep last 1000 snapshots
            alerts: Vec::new(),
            system_metrics: SystemMetrics {
                latency_percentiles: LatencyPercentiles {
                    p50_us: 0,
                    p95_us: 0,
                    p99_us: 0,
                    p999_us: 0,
                    max_us: 0,
                },
                throughput_metrics: ThroughputMetrics {
                    tps: 0.0,
                    ops: 0.0,
                    sps: 0.0,
                    peak_tps: 0.0,
                },
                resource_utilization: ResourceUtilization {
                    cpu_percent: 0.0,
                    memory_percent: 0.0,
                    network_percent: 0.0,
                    disk_percent: 0.0,
                },
                error_rates: ErrorRates {
                    overall_percent: 0.0,
                    network_percent: 0.0,
                    computation_percent: 0.0,
                    timeout_percent: 0.0,
                },
                timestamp: Utc::now(),
            },
        })
    }
    
    /// Start tracking a new operation
    pub async fn start_operation(&mut self, operation_id: &str) -> Result<OperationTracker, Box<dyn std::error::Error + Send + Sync>> {
        debug!("Starting performance tracking for operation: {}", operation_id);
        
        let tracker = OperationTracker {
            operation_id: operation_id.to_string(),
            start_time: std::time::Instant::now(),
            operation_type: "mpc_signature".to_string(),
            checkpoints: Vec::new(),
            resource_usage: ResourceUsage {
                peak_memory_bytes: 0,
                cpu_time_us: 0,
                network_io_bytes: 0,
                disk_io_ops: 0,
                thread_count: 1,
            },
        };
        
        self.active_operations.insert(operation_id.to_string(), tracker.clone());
        Ok(tracker)
    }
    
    /// Add checkpoint to operation tracking
    pub async fn add_checkpoint(
        &mut self,
        operation_id: &str,
        checkpoint_name: &str,
        additional_metrics: HashMap<String, f64>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let memory_usage_bytes = self.get_current_memory_usage();
        if let Some(tracker) = self.active_operations.get_mut(operation_id) {
            let elapsed = tracker.start_time.elapsed();
            let checkpoint = PerformanceCheckpoint {
                name: checkpoint_name.to_string(),
                timestamp: Utc::now(),
                elapsed_us: elapsed.as_micros() as u64,
                memory_usage_bytes,
                metrics: additional_metrics,
            };
            
            tracker.checkpoints.push(checkpoint);
            debug!("Added checkpoint '{}' to operation {} at {}μs", 
                   checkpoint_name, operation_id, elapsed.as_micros());
        }
        
        Ok(())
    }
    
    /// Complete operation tracking
    pub async fn complete_operation(
        &mut self,
        operation_id: &str,
        final_metrics: &PerformanceMetrics,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if let Some(tracker) = self.active_operations.remove(operation_id) {
            let total_duration = tracker.start_time.elapsed();
            
            info!("Operation {} completed in {:?}", operation_id, total_duration);
            
            // Update system metrics
            self.update_system_metrics(final_metrics).await?;
            
            // Check for performance alerts
            self.check_performance_alerts(final_metrics).await?;
            
            // Check for performance regressions
            if self.config.enable_regression_detection {
                self.check_performance_regression(final_metrics).await?;
            }
        }
        
        Ok(())
    }
    
    /// Update system-wide performance metrics
    async fn update_system_metrics(&mut self, metrics: &PerformanceMetrics) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        // Update latency percentiles (simplified implementation)
        self.system_metrics.latency_percentiles.p50_us = metrics.total_latency_us;
        self.system_metrics.latency_percentiles.p95_us = (metrics.total_latency_us as f64 * 1.2) as u64;
        self.system_metrics.latency_percentiles.p99_us = (metrics.total_latency_us as f64 * 1.5) as u64;
        self.system_metrics.latency_percentiles.p999_us = (metrics.total_latency_us as f64 * 2.0) as u64;
        
        if metrics.total_latency_us > self.system_metrics.latency_percentiles.max_us {
            self.system_metrics.latency_percentiles.max_us = metrics.total_latency_us;
        }
        
        // Update throughput metrics
        self.system_metrics.throughput_metrics.tps = metrics.throughput_ops;
        self.system_metrics.throughput_metrics.ops = metrics.throughput_ops;
        self.system_metrics.throughput_metrics.sps = metrics.throughput_ops;
        
        if metrics.throughput_ops > self.system_metrics.throughput_metrics.peak_tps {
            self.system_metrics.throughput_metrics.peak_tps = metrics.throughput_ops;
        }
        
        // Update resource utilization (mock values)
        self.system_metrics.resource_utilization.cpu_percent = 
            (metrics.computation_time_us as f64 / metrics.total_latency_us as f64) * 100.0;
        self.system_metrics.resource_utilization.memory_percent = 
            (metrics.memory_usage_bytes as f64 / (1024.0 * 1024.0 * 1024.0)) * 100.0; // Assume 1GB total
        self.system_metrics.resource_utilization.network_percent = 
            (metrics.network_latency_us as f64 / metrics.total_latency_us as f64) * 100.0;
        
        self.system_metrics.timestamp = Utc::now();
        
        Ok(())
    }
    
    /// Check for performance alerts
    async fn check_performance_alerts(&mut self, metrics: &PerformanceMetrics) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let max_latency_us = self.config.alert_thresholds.max_latency_us;
        let min_throughput_tps = self.config.alert_thresholds.min_throughput_tps;
        let max_memory_mb = self.config.alert_thresholds.max_memory_mb;
        
        // Check latency threshold
        if metrics.total_latency_us > max_latency_us {
            self.create_alert(
                AlertSeverity::Warning,
                AlertType::LatencyThreshold,
                format!("Latency {}μs exceeds threshold {}μs", 
                       metrics.total_latency_us, max_latency_us),
                vec!["total_latency_us".to_string()],
                vec!["Investigate network latency".to_string(), "Check computational load".to_string()],
            ).await?;
        }
        
        // Check throughput threshold
        if metrics.throughput_ops < min_throughput_tps as f64 {
            self.create_alert(
                AlertSeverity::Warning,
                AlertType::ThroughputBelow,
                format!("Throughput {:.2} TPS below threshold {} TPS", 
                       metrics.throughput_ops, min_throughput_tps),
                vec!["throughput_ops".to_string()],
                vec!["Scale up resources".to_string(), "Optimize algorithms".to_string()],
            ).await?;
        }
        
        // Check memory usage
        if metrics.memory_usage_bytes > max_memory_mb * 1024 * 1024 {
            self.create_alert(
                AlertSeverity::Critical,
                AlertType::ResourceUtilizationHigh,
                format!("Memory usage {} MB exceeds threshold {} MB", 
                       metrics.memory_usage_bytes / (1024 * 1024), max_memory_mb),
                vec!["memory_usage_bytes".to_string()],
                vec!["Increase memory allocation".to_string(), "Optimize memory usage".to_string()],
            ).await?;
        }
        
        Ok(())
    }
    
    /// Check for performance regression
    async fn check_performance_regression(&mut self, current_metrics: &PerformanceMetrics) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        if self.historical_data.len() < 10 {
            return Ok(()); // Need more data for regression analysis
        }
        
        // Calculate baseline from historical data
        let recent_snapshots: Vec<&PerformanceSnapshot> = self.historical_data
            .iter()
            .rev()
            .take(10)
            .collect();
        
        let baseline_latency: u64 = recent_snapshots
            .iter()
            .map(|s| s.system_metrics.latency_percentiles.p95_us)
            .sum::<u64>() / recent_snapshots.len() as u64;
        
        let baseline_throughput: f64 = recent_snapshots
            .iter()
            .map(|s| s.system_metrics.throughput_metrics.tps)
            .sum::<f64>() / recent_snapshots.len() as f64;
        
        // Check for significant regression (20% degradation)
        let latency_regression = current_metrics.total_latency_us as f64 > baseline_latency as f64 * 1.2;
        let throughput_regression = current_metrics.throughput_ops < baseline_throughput * 0.8;
        
        if latency_regression || throughput_regression {
            self.create_alert(
                AlertSeverity::Critical,
                AlertType::PerformanceRegression,
                format!("Performance regression detected: latency={}, throughput={}", 
                       latency_regression, throughput_regression),
                vec!["latency".to_string(), "throughput".to_string()],
                vec![
                    "Review recent changes".to_string(),
                    "Compare with baseline performance".to_string(),
                    "Consider rollback if severe".to_string(),
                ],
            ).await?;
        }
        
        Ok(())
    }
    
    /// Create a performance alert
    async fn create_alert(
        &mut self,
        severity: AlertSeverity,
        alert_type: AlertType,
        message: String,
        affected_metrics: Vec<String>,
        recommended_actions: Vec<String>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let alert = PerformanceAlert {
            alert_id: uuid::Uuid::new_v4().to_string(),
            severity: severity.clone(),
            alert_type,
            message: message.clone(),
            timestamp: Utc::now(),
            affected_metrics,
            recommended_actions,
        };
        
        match severity {
            AlertSeverity::Critical => error!("CRITICAL PERFORMANCE ALERT: {}", message),
            AlertSeverity::Warning => warn!("PERFORMANCE WARNING: {}", message),
            AlertSeverity::Info => info!("PERFORMANCE INFO: {}", message),
        }
        
        self.alerts.push(alert);
        
        // Keep only last 100 alerts
        if self.alerts.len() > 100 {
            self.alerts.remove(0);
        }
        
        Ok(())
    }
    
    /// Get current system metrics
    pub async fn get_system_metrics(&self) -> Result<SystemMetrics, Box<dyn std::error::Error + Send + Sync>> {
        Ok(self.system_metrics.clone())
    }
    
    /// Get recent performance alerts
    pub async fn get_recent_alerts(&self, count: usize) -> Vec<PerformanceAlert> {
        self.alerts
            .iter()
            .rev()
            .take(count)
            .cloned()
            .collect()
    }
    
    /// Take performance snapshot for historical analysis
    pub async fn take_snapshot(&mut self) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let snapshot = PerformanceSnapshot {
            timestamp: Utc::now(),
            system_metrics: self.system_metrics.clone(),
            operation_stats: OperationStatistics {
                total_operations: 0, // Would be tracked in real implementation
                successful_operations: 0,
                failed_operations: 0,
                avg_operation_time_us: self.system_metrics.latency_percentiles.p50_us,
                operations_by_type: HashMap::new(),
            },
            alert_summary: AlertSummary {
                total_alerts: self.alerts.len() as u64,
                critical_alerts: self.alerts.iter().filter(|a| matches!(a.severity, AlertSeverity::Critical)).count() as u64,
                warning_alerts: self.alerts.iter().filter(|a| matches!(a.severity, AlertSeverity::Warning)).count() as u64,
                regression_alerts: self.alerts.iter().filter(|a| matches!(a.alert_type, AlertType::PerformanceRegression)).count() as u64,
            },
        };
        
        self.historical_data.push_back(snapshot);
        
        // Keep only last 1000 snapshots
        if self.historical_data.len() > 1000 {
            self.historical_data.pop_front();
        }
        
        Ok(())
    }
    
    /// Get current memory usage (mock implementation)
    fn get_current_memory_usage(&self) -> usize {
        // In production, this would use actual system metrics
        1024 * 1024 * 64 // 64 MB mock value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::AlertThresholds;
    
    #[tokio::test]
    async fn test_performance_monitor_creation() {
        let config = PerformanceConfig {
            enable_latency_tracking: true,
            metrics_interval_ms: 1000,
            enable_regression_detection: true,
            alert_thresholds: AlertThresholds {
                max_latency_us: 50_000,
                min_throughput_tps: 500,
                max_error_rate_percent: 1.0,
                max_memory_mb: 1024,
            },
        };
        
        let monitor = PerformanceMonitor::new(config).await;
        assert!(monitor.is_ok());
    }
    
    #[tokio::test]
    async fn test_operation_tracking() {
        let config = PerformanceConfig {
            enable_latency_tracking: true,
            metrics_interval_ms: 1000,
            enable_regression_detection: false,
            alert_thresholds: AlertThresholds {
                max_latency_us: 50_000,
                min_throughput_tps: 500,
                max_error_rate_percent: 1.0,
                max_memory_mb: 1024,
            },
        };
        
        let mut monitor = PerformanceMonitor::new(config).await.unwrap();
        
        let operation_id = "test-op-001";
        let tracker = monitor.start_operation(operation_id).await.unwrap();
        assert_eq!(tracker.operation_id, operation_id);
        
        // Add checkpoint
        let mut additional_metrics = HashMap::new();
        additional_metrics.insert("test_metric".to_string(), 42.0);
        
        let result = monitor.add_checkpoint(operation_id, "test_checkpoint", additional_metrics).await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_performance_alerts() {
        let config = PerformanceConfig {
            enable_latency_tracking: true,
            metrics_interval_ms: 1000,
            enable_regression_detection: false,
            alert_thresholds: AlertThresholds {
                max_latency_us: 1000, // Low threshold for testing
                min_throughput_tps: 1000, // High threshold for testing
                max_error_rate_percent: 1.0,
                max_memory_mb: 1,
            },
        };
        
        let mut monitor = PerformanceMonitor::new(config).await.unwrap();
        
        let metrics = PerformanceMetrics {
            total_latency_us: 5000, // Exceeds threshold
            network_latency_us: 1000,
            computation_time_us: 4000,
            memory_usage_bytes: 1024 * 1024 * 512, // 512 MB
            network_rounds: 3,
            throughput_ops: 100.0, // Below threshold
        };
        
        let result = monitor.check_performance_alerts(&metrics).await;
        assert!(result.is_ok());
        
        // Should have generated alerts
        let alerts = monitor.get_recent_alerts(10).await;
        assert!(!alerts.is_empty());
    }
    
    #[tokio::test]
    async fn test_performance_snapshot() {
        let config = PerformanceConfig {
            enable_latency_tracking: true,
            metrics_interval_ms: 1000,
            enable_regression_detection: false,
            alert_thresholds: AlertThresholds {
                max_latency_us: 50_000,
                min_throughput_tps: 500,
                max_error_rate_percent: 1.0,
                max_memory_mb: 1024,
            },
        };
        
        let mut monitor = PerformanceMonitor::new(config).await.unwrap();
        
        let result = monitor.take_snapshot().await;
        assert!(result.is_ok());
        
        // Should have one snapshot
        assert_eq!(monitor.historical_data.len(), 1);
    }
}
