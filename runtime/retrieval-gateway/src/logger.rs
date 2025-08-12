use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::VecDeque,
    sync::Arc,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tokio::{
    sync::{Mutex, RwLock},
    time::interval,
};
use tonic::{transport::Channel, Request};
use uuid::Uuid;
use zstd::{encode_all, Decoder};

// Protobuf definitions (simplified for this implementation)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub id: String,
    pub timestamp: u64,
    pub level: LogLevel,
    pub message: String,
    pub metadata: std::collections::HashMap<String, String>,
    pub tenant: String,
    pub service: String,
    pub trace_id: Option<String>,
    pub span_id: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchLogRequest {
    pub entries: Vec<LogEntry>,
    pub batch_id: String,
    pub tenant: String,
    pub compressed: bool,
    pub compression_algorithm: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchLogResponse {
    pub batch_id: String,
    pub success: bool,
    pub processed_count: usize,
    pub error_message: Option<String>,
}

/// Logger configuration
#[derive(Debug, Clone)]
pub struct LoggerConfig {
    /// Batch size for committing logs
    pub batch_size: usize,
    
    /// Batch timeout in milliseconds
    pub batch_timeout_ms: u64,
    
    /// Zstd compression level (1-22)
    pub compression_level: i32,
    
    /// Enable protobuf encoding
    pub enable_protobuf: bool,
    
    /// Enable flatbuffers encoding
    pub enable_flatbuffers: bool,
    
    /// Fallback to JSON on ingest failure
    pub enable_json_fallback: bool,
    
    /// Maximum retry attempts
    pub max_retries: u32,
    
    /// Retry delay in milliseconds
    pub retry_delay_ms: u64,
    
    /// Ledger endpoint for log ingestion
    pub ledger_endpoint: String,
    
    /// Enable structured logging
    pub enable_structured_logging: bool,
    
    /// Enable trace correlation
    pub enable_trace_correlation: bool,
}

impl Default for LoggerConfig {
    fn default() -> Self {
        Self {
            batch_size: 100,
            batch_timeout_ms: 1000,
            compression_level: 6,
            enable_protobuf: true,
            enable_flatbuffers: false,
            enable_json_fallback: true,
            max_retries: 3,
            retry_delay_ms: 1000,
            ledger_endpoint: "http://localhost:3000".to_string(),
            enable_structured_logging: true,
            enable_trace_correlation: true,
        }
    }
}

/// Structured logger with protobuf/flatbuffers support
pub struct StructuredLogger {
    /// Configuration
    config: LoggerConfig,
    
    /// Batch buffer
    batch_buffer: Arc<Mutex<VecDeque<LogEntry>>>,
    
    /// Background batch processor
    batch_processor: Option<tokio::task::JoinHandle<()>>,
    
    /// Statistics
    stats: Arc<RwLock<LoggerStats>>,
    
    /// Current trace context
    trace_context: Arc<RwLock<TraceContext>>,
}

/// Logger statistics
#[derive(Debug, Clone, Default)]
pub struct LoggerStats {
    pub total_logs_processed: u64,
    pub total_batches_sent: u64,
    pub total_compression_savings_bytes: u64,
    pub total_ingest_time_ms: u64,
    pub failed_batches: u64,
    pub fallback_to_json_count: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
}

/// Trace context for correlation
#[derive(Debug, Clone, Default)]
pub struct TraceContext {
    pub trace_id: Option<String>,
    pub span_id: Option<String>,
    pub parent_span_id: Option<String>,
}

impl StructuredLogger {
    /// Create a new structured logger
    pub async fn new(config: Option<LoggerConfig>) -> Result<Self> {
        let config = config.unwrap_or_default();
        
        let logger = Self {
            config: config.clone(),
            batch_buffer: Arc::new(Mutex::new(VecDeque::new())),
            batch_processor: None,
            stats: Arc::new(RwLock::new(LoggerStats::default())),
            trace_context: Arc::new(RwLock::new(TraceContext::default())),
        };
        
        // Start background batch processor
        let batch_processor = logger.start_batch_processor().await?;
        
        Ok(Self {
            batch_processor: Some(batch_processor),
            ..logger
        })
    }
    
    /// Start background batch processor
    async fn start_batch_processor(&self) -> Result<tokio::task::JoinHandle<()>> {
        let batch_buffer = self.batch_buffer.clone();
        let config = self.config.clone();
        let stats = self.stats.clone();
        
        let handle = tokio::spawn(async move {
            let mut interval = interval(Duration::from_millis(config.batch_timeout_ms));
            
            loop {
                interval.tick().await;
                
                // Process batch if buffer is not empty
                let mut buffer = batch_buffer.lock().await;
                if !buffer.is_empty() {
                    let entries: Vec<LogEntry> = buffer.drain(..).collect();
                    drop(buffer); // Release lock before async operation
                    
                    if let Err(e) = Self::process_batch(&config, &stats, entries).await {
                        eprintln!("Failed to process log batch: {}", e);
                    }
                }
            }
        });
        
        Ok(handle)
    }
    
    /// Process a batch of log entries
    async fn process_batch(
        config: &LoggerConfig,
        stats: &Arc<RwLock<LoggerStats>>,
        entries: Vec<LogEntry>,
    ) -> Result<()> {
        let start_time = Instant::now();
        
        // Try protobuf first
        if config.enable_protobuf {
            match Self::send_protobuf_batch(config, entries.clone()).await {
                Ok(_) => {
                    Self::update_stats(stats, entries.len(), start_time.elapsed(), 0).await;
                    return Ok(());
                }
                Err(e) => {
                    eprintln!("Protobuf logging failed: {}", e);
                }
            }
        }
        
        // Try flatbuffers if protobuf failed
        if config.enable_flatbuffers {
            match Self::send_flatbuffers_batch(config, entries.clone()).await {
                Ok(_) => {
                    Self::update_stats(stats, entries.len(), start_time.elapsed(), 0).await;
                    return Ok(());
                }
                Err(e) => {
                    eprintln!("Flatbuffers logging failed: {}", e);
                }
            }
        }
        
        // Fallback to JSON if enabled
        if config.enable_json_fallback {
            match Self::send_json_batch(config, entries.clone()).await {
                Ok(_) => {
                    Self::update_stats(stats, entries.len(), start_time.elapsed(), 0).await;
                    Self::increment_fallback_count(stats).await;
                    return Ok(());
                }
                Err(e) => {
                    eprintln!("JSON fallback also failed: {}", e);
                }
            }
        }
        
        // All methods failed
        Self::increment_failed_batches(stats).await;
        Err(anyhow::anyhow!("All logging methods failed"))
    }
    
    /// Send batch using protobuf encoding
    async fn send_protobuf_batch(
        _config: &LoggerConfig,
        entries: Vec<LogEntry>,
    ) -> Result<()> {
        // In a real implementation, this would use tonic/prost for protobuf
        // For now, we'll simulate the protobuf encoding
        let batch = BatchLogRequest {
            entries,
            batch_id: Uuid::new_v4().to_string(),
            tenant: "default".to_string(),
            compressed: false,
            compression_algorithm: "none".to_string(),
        };
        
        // Simulate protobuf serialization
        let _serialized = serde_json::to_vec(&batch)
            .context("Failed to serialize batch")?;
        
        // Simulate gRPC call
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        Ok(())
    }
    
    /// Send batch using flatbuffers encoding
    async fn send_flatbuffers_batch(
        _config: &LoggerConfig,
        entries: Vec<LogEntry>,
    ) -> Result<()> {
        // In a real implementation, this would use flatbuffers
        // For now, we'll simulate the flatbuffers encoding
        let batch = BatchLogRequest {
            entries,
            batch_id: Uuid::new_v4().to_string(),
            tenant: "default".to_string(),
            compressed: false,
            compression_algorithm: "none".to_string(),
        };
        
        // Simulate flatbuffers serialization
        let _serialized = serde_json::to_vec(&batch)
            .context("Failed to serialize batch")?;
        
        // Simulate gRPC call
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        Ok(())
    }
    
    /// Send batch using JSON encoding (fallback)
    async fn send_json_batch(
        _config: &LoggerConfig,
        entries: Vec<LogEntry>,
    ) -> Result<()> {
        let batch = BatchLogRequest {
            entries,
            batch_id: Uuid::new_v4().to_string(),
            tenant: "default".to_string(),
            compressed: false,
            compression_algorithm: "none".to_string(),
        };
        
        // Simulate JSON serialization
        let _serialized = serde_json::to_vec(&batch)
            .context("Failed to serialize batch")?;
        
        // Simulate gRPC call
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        Ok(())
    }
    
    /// Log a message at debug level
    pub async fn debug(&self, message: &str, tenant: &str, metadata: Option<std::collections::HashMap<String, String>>) -> Result<()> {
        self.log(LogLevel::Debug, message, tenant, metadata).await
    }
    
    /// Log a message at info level
    pub async fn info(&self, message: &str, tenant: &str, metadata: Option<std::collections::HashMap<String, String>>) -> Result<()> {
        self.log(LogLevel::Info, message, tenant, metadata).await
    }
    
    /// Log a message at warn level
    pub async fn warn(&self, message: &str, tenant: &str, metadata: Option<std::collections::HashMap<String, String>>) -> Result<()> {
        self.log(LogLevel::Warn, message, tenant, metadata).await
    }
    
    /// Log a message at error level
    pub async fn error(&self, message: &str, tenant: &str, metadata: Option<std::collections::HashMap<String, String>>) -> Result<()> {
        self.log(LogLevel::Error, message, tenant, metadata).await
    }
    
    /// Log a message at fatal level
    pub async fn fatal(&self, message: &str, tenant: &str, metadata: Option<std::collections::HashMap<String, String>>) -> Result<()> {
        self.log(LogLevel::Fatal, message, tenant, metadata).await
    }
    
    /// Internal log method
    async fn log(
        &self,
        level: LogLevel,
        message: &str,
        tenant: &str,
        metadata: Option<std::collections::HashMap<String, String>>,
    ) -> Result<()> {
        let trace_context = self.trace_context.read().await;
        
        let entry = LogEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            level,
            message: message.to_string(),
            metadata: metadata.unwrap_or_default(),
            tenant: tenant.to_string(),
            service: "retrieval-gateway".to_string(),
            trace_id: trace_context.trace_id.clone(),
            span_id: trace_context.span_id.clone(),
        };
        
        // Add to batch buffer
        let mut buffer = self.batch_buffer.lock().await;
        
        // Check if we need to process batch immediately
        if buffer.len() >= self.config.batch_size {
            let entries: Vec<LogEntry> = buffer.drain(..).collect();
            drop(buffer); // Release lock before async operation
            
            // Process batch immediately
            let config = self.config.clone();
            let stats = self.stats.clone();
            
            tokio::spawn(async move {
                if let Err(e) = Self::process_batch(&config, &stats, entries).await {
                    eprintln!("Failed to process immediate log batch: {}", e);
                }
            });
        }
        
        // Add to buffer
        buffer.push_back(entry);
        Ok(())
    }
    
    /// Set trace context for correlation
    pub async fn set_trace_context(&self, trace_id: Option<String>, span_id: Option<String>, parent_span_id: Option<String>) {
        let mut context = self.trace_context.write().await;
        context.trace_id = trace_id;
        context.span_id = span_id;
        context.parent_span_id = parent_span_id;
    }
    
    /// Get logger statistics
    pub async fn get_stats(&self) -> LoggerStats {
        self.stats.read().await.clone()
    }
    
    /// Update statistics
    async fn update_stats(
        stats: &Arc<RwLock<LoggerStats>>,
        entries_count: usize,
        duration: Duration,
        compression_savings: u64,
    ) {
        let mut stats = stats.write().await;
        stats.total_logs_processed += entries_count as u64;
        stats.total_batches_sent += 1;
        stats.total_compression_savings_bytes += compression_savings;
        stats.total_ingest_time_ms += duration.as_millis() as u64;
    }
    
    /// Increment fallback count
    async fn increment_fallback_count(stats: &Arc<RwLock<LoggerStats>>) {
        let mut stats = stats.write().await;
        stats.fallback_to_json_count += 1;
    }
    
    /// Increment failed batches count
    async fn increment_failed_batches(stats: &Arc<RwLock<LoggerStats>>) {
        let mut stats = stats.write().await;
        stats.failed_batches += 1;
    }
}

impl Drop for StructuredLogger {
    fn drop(&mut self) {
        if let Some(handle) = self.batch_processor.take() {
            handle.abort();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    
    #[tokio::test]
    async fn test_logger_creation() {
        let config = LoggerConfig {
            batch_size: 10,
            batch_timeout_ms: 100,
            ..Default::default()
        };
        
        let logger = StructuredLogger::new(Some(config)).await.unwrap();
        assert!(logger.batch_processor.is_some());
    }
    
    #[tokio::test]
    async fn test_logging() {
        let logger = StructuredLogger::new(None).await.unwrap();
        
        let mut metadata = HashMap::new();
        metadata.insert("user_id".to_string(), "123".to_string());
        
        // Test info logging
        logger.info("Test info message", "test-tenant", Some(metadata.clone())).await.unwrap();
        
        // Test error logging
        logger.error("Test error message", "test-tenant", Some(metadata)).await.unwrap();
        
        // Wait a bit for batch processing
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        let stats = logger.get_stats().await;
        assert!(stats.total_logs_processed > 0);
    }
    
    #[tokio::test]
    async fn test_trace_context() {
        let logger = StructuredLogger::new(None).await.unwrap();
        
        logger.set_trace_context(
            Some("trace-123".to_string()),
            Some("span-456".to_string()),
            Some("parent-789".to_string()),
        ).await;
        
        // Test logging with trace context
        logger.info("Test trace message", "test-tenant", None).await.unwrap();
        
        // Wait for batch processing
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        let stats = logger.get_stats().await;
        assert!(stats.total_logs_processed > 0);
    }
    
    #[test]
    fn test_compression() {
        let data = b"test data for compression";
        let compressed = encode_all(data, 6).unwrap();
        
        assert!(compressed.len() < data.len());
        
        let decompressed = Decoder::new(&compressed[..]).unwrap()
            .read_to_end(&mut Vec::new())
            .unwrap();
        
        assert_eq!(decompressed, data);
    }
}
