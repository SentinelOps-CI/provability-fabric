use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::{
    collections::VecDeque,
    sync::Arc,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
use tokio::{
    sync::{mpsc, Mutex, RwLock},
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

/// Ingest configuration
#[derive(Debug, Clone)]
pub struct IngestConfig {
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
}

impl Default for IngestConfig {
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
        }
    }
}

/// Ledger ingest service client
pub struct LedgerIngestClient {
    /// gRPC channel to ledger service
    channel: Channel,
    
    /// Configuration
    config: IngestConfig,
    
    /// Batch buffer
    batch_buffer: Arc<Mutex<VecDeque<LogEntry>>>,
    
    /// Background batch processor
    batch_processor: Option<tokio::task::JoinHandle<()>>,
    
    /// Statistics
    stats: Arc<RwLock<IngestStats>>,
}

/// Ingest statistics
#[derive(Debug, Clone, Default)]
pub struct IngestStats {
    pub total_logs_processed: u64,
    pub total_batches_sent: u64,
    pub total_compression_savings_bytes: u64,
    pub total_ingest_time_ms: u64,
    pub failed_batches: u64,
    pub fallback_to_json_count: u64,
}

impl LedgerIngestClient {
    /// Create a new ledger ingest client
    pub async fn new(
        ledger_endpoint: String,
        config: Option<IngestConfig>,
    ) -> Result<Self> {
        let config = config.unwrap_or_default();
        
        // Create gRPC channel
        let channel = Channel::from_shared(ledger_endpoint)
            .context("Invalid ledger endpoint")?
            .connect()
            .await
            .context("Failed to connect to ledger")?;
        
        let client = Self {
            channel,
            config,
            batch_buffer: Arc::new(Mutex::new(VecDeque::new())),
            batch_processor: None,
            stats: Arc::new(RwLock::new(IngestStats::default())),
        };
        
        // Start background batch processor
        let batch_processor = client.start_batch_processor().await?;
        
        Ok(Self {
            batch_processor: Some(batch_processor),
            ..client
        })
    }
    
    /// Start background batch processor
    async fn start_batch_processor(&self) -> Result<tokio::task::JoinHandle<()>> {
        let batch_buffer = self.batch_buffer.clone();
        let config = self.config.clone();
        let stats = self.stats.clone();
        let channel = self.channel.clone();
        
        let handle = tokio::spawn(async move {
            let mut interval = interval(Duration::from_millis(config.batch_timeout_ms));
            
            loop {
                interval.tick().await;
                
                // Process batch if buffer is not empty
                let mut buffer = batch_buffer.lock().await;
                if !buffer.is_empty() {
                    let entries: Vec<LogEntry> = buffer.drain(..).collect();
                    drop(buffer); // Release lock before async operation
                    
                    if let Err(e) = Self::process_batch(
                        &channel,
                        &config,
                        &stats,
                        entries,
                    ).await {
                        eprintln!("Failed to process batch: {}", e);
                    }
                }
            }
        });
        
        Ok(handle)
    }
    
    /// Process a batch of log entries
    async fn process_batch(
        channel: &Channel,
        config: &IngestConfig,
        stats: &Arc<RwLock<IngestStats>>,
        entries: Vec<LogEntry>,
    ) -> Result<()> {
        let start_time = Instant::now();
        
        // Try protobuf first
        if config.enable_protobuf {
            match Self::send_protobuf_batch(channel, config, entries.clone()).await {
                Ok(_) => {
                    Self::update_stats(stats, entries.len(), start_time.elapsed(), 0).await;
                    return Ok(());
                }
                Err(e) => {
                    eprintln!("Protobuf ingest failed: {}", e);
                }
            }
        }
        
        // Try flatbuffers if protobuf failed
        if config.enable_flatbuffers {
            match Self::send_flatbuffers_batch(channel, config, entries.clone()).await {
                Ok(_) => {
                    Self::update_stats(stats, entries.len(), start_time.elapsed(), 0).await;
                    return Ok(());
                }
                Err(e) => {
                    eprintln!("Flatbuffers ingest failed: {}", e);
                }
            }
        }
        
        // Fallback to JSON if enabled
        if config.enable_json_fallback {
            match Self::send_json_batch(channel, config, entries.clone()).await {
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
        Err(anyhow::anyhow!("All ingest methods failed"))
    }
    
    /// Send batch using protobuf encoding
    async fn send_protobuf_batch(
        _channel: &Channel,
        _config: &IngestConfig,
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
        _channel: &Channel,
        _config: &IngestConfig,
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
        _channel: &Channel,
        _config: &IngestConfig,
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
    
    /// Add a log entry to the batch buffer
    pub async fn add_log(&self, entry: LogEntry) -> Result<()> {
        let mut buffer = self.batch_buffer.lock().await;
        
        // Check if we need to process batch immediately
        if buffer.len() >= self.config.batch_size {
            let entries: Vec<LogEntry> = buffer.drain(..).collect();
            drop(buffer); // Release lock before async operation
            
            // Process batch immediately
            let config = self.config.clone();
            let stats = self.stats.clone();
            let channel = self.channel.clone();
            
            tokio::spawn(async move {
                if let Err(e) = Self::process_batch(&channel, &config, &stats, entries).await {
                    eprintln!("Failed to process immediate batch: {}", e);
                }
            });
        }
        
        // Add to buffer
        buffer.push_back(entry);
        Ok(())
    }
    
    /// Get ingest statistics
    pub async fn get_stats(&self) -> IngestStats {
        self.stats.read().await.clone()
    }
    
    /// Update statistics
    async fn update_stats(
        stats: &Arc<RwLock<IngestStats>>,
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
    async fn increment_fallback_count(stats: &Arc<RwLock<IngestStats>>) {
        let mut stats = stats.write().await;
        stats.fallback_to_json_count += 1;
    }
    
    /// Increment failed batches count
    async fn increment_failed_batches(stats: &Arc<RwLock<IngestStats>>) {
        let mut stats = stats.write().await;
        stats.failed_batches += 1;
    }
}

impl Drop for LedgerIngestClient {
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
    async fn test_ingest_client_creation() {
        let config = IngestConfig {
            batch_size: 10,
            batch_timeout_ms: 100,
            ..Default::default()
        };
        
        // This would fail in tests without a real ledger endpoint
        // In real tests, we'd use a mock server
        let result = LedgerIngestClient::new("http://localhost:3000".to_string(), Some(config)).await;
        assert!(result.is_err()); // Expected to fail without real server
    }
    
    #[test]
    fn test_log_entry_creation() {
        let mut metadata = HashMap::new();
        metadata.insert("service".to_string(), "test-service".to_string());
        
        let entry = LogEntry {
            id: Uuid::new_v4().to_string(),
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            level: LogLevel::Info,
            message: "Test log message".to_string(),
            metadata,
            tenant: "test-tenant".to_string(),
            service: "test-service".to_string(),
        };
        
        assert_eq!(entry.level as i32, LogLevel::Info as i32);
        assert_eq!(entry.tenant, "test-tenant");
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
