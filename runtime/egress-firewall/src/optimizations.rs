//! Rust hot-path hygiene optimizations for egress-firewall
//! 
//! This module implements performance optimizations including:
//! - Zero-copy deserialization with serde(borrow)
//! - Efficient data structures with minimal allocations
//! - Optimized string handling
//! - Memory pool management
//! - Performance profiling integration

use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;
use bytes::{Bytes, BytesMut, Buf, BufMut};
use serde::{Deserialize, Serialize, Deserializer, Serializer};
use dashmap::DashMap;
use crossbeam_channel::{bounded, Sender, Receiver};
use rayon::prelude::*;
use std::time::{Duration, Instant};

/// Zero-copy text data for efficient processing
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ZeroCopyText<'a> {
    data: &'a [u8],
    hash: u64,
}

impl<'a> ZeroCopyText<'a> {
    /// Create zero-copy text from bytes
    pub fn new(data: &'a [u8]) -> Self {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        data.hash(&mut hasher);
        let hash = hasher.finish();
        
        Self { data, hash }
    }
    
    /// Get text as bytes slice
    pub fn as_bytes(&self) -> &[u8] {
        self.data
    }
    
    /// Get text as string slice (if valid UTF-8)
    pub fn as_str(&self) -> Option<&str> {
        std::str::from_utf8(self.data).ok()
    }
    
    /// Get pre-computed hash
    pub fn hash(&self) -> u64 {
        self.hash
    }
    
    /// Check if text contains pattern (zero-copy)
    pub fn contains_pattern(&self, pattern: &[u8]) -> bool {
        self.data.windows(pattern.len()).any(|window| window == pattern)
    }
    
    /// Find pattern position (zero-copy)
    pub fn find_pattern(&self, pattern: &[u8]) -> Option<usize> {
        self.data.windows(pattern.len())
            .position(|window| window == pattern)
    }
}

/// Efficient text processing pipeline with zero-copy operations
pub struct TextProcessor {
    patterns: Arc<DashMap<u64, Vec<u8>>>,
    cache: Arc<DashMap<u64, ProcessingResult>>,
    pool: Arc<MemoryPool>,
    metrics: Arc<RwLock<ProcessingMetrics>>,
}

/// Processing result with minimal allocations
#[derive(Debug, Clone)]
pub struct ProcessingResult {
    pub matches: Vec<Match>,
    pub processing_time_ns: u64,
    pub cache_hit: bool,
}

/// Pattern match with position information
#[derive(Debug, Clone)]
pub struct Match {
    pub pattern_id: u64,
    pub start: usize,
    pub end: usize,
    pub confidence: f32,
}

/// Memory pool for efficient allocation management
pub struct MemoryPool {
    buffers: Arc<DashMap<usize, Vec<BytesMut>>>,
    max_pool_size: usize,
}

impl MemoryPool {
    /// Create new memory pool
    pub fn new(max_pool_size: usize) -> Self {
        Self {
            buffers: Arc::new(DashMap::new()),
            max_pool_size,
        }
    }
    
    /// Get buffer from pool or create new one
    pub fn get_buffer(&self, size: usize) -> BytesMut {
        if let Some(mut buffers) = self.buffers.get_mut(&size) {
            if let Some(buffer) = buffers.pop() {
                buffer.clear();
                return buffer;
            }
        }
        
        BytesMut::with_capacity(size)
    }
    
    /// Return buffer to pool
    pub fn return_buffer(&self, mut buffer: BytesMut) {
        let size = buffer.capacity();
        if let Some(mut buffers) = self.buffers.get_mut(&size) {
            if buffers.len() < self.max_pool_size {
                buffer.clear();
                buffers.push(buffer);
            }
        }
    }
}

/// Processing metrics for performance monitoring
#[derive(Debug, Clone, Default)]
pub struct ProcessingMetrics {
    pub total_requests: u64,
    pub cache_hits: u64,
    pub average_processing_time_ns: u64,
    pub total_matches_found: u64,
    pub memory_pool_hits: u64,
}

impl TextProcessor {
    /// Create new text processor
    pub fn new() -> Self {
        Self {
            patterns: Arc::new(DashMap::new()),
            cache: Arc::new(DashMap::new()),
            pool: Arc::new(MemoryPool::new(1000)),
            metrics: Arc::new(RwLock::new(ProcessingMetrics::default())),
        }
    }
    
    /// Add pattern to processor (zero-copy)
    pub fn add_pattern(&self, pattern_id: u64, pattern: Vec<u8>) {
        self.patterns.insert(pattern_id, pattern);
    }
    
    /// Process text with zero-copy optimizations
    pub fn process_text<'a>(&self, text: &'a [u8]) -> ProcessingResult {
        let start_time = Instant::now();
        
        // Check cache first
        let text_hash = {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut hasher = DefaultHasher::new();
            text.hash(&mut hasher);
            hasher.finish()
        };
        
        if let Some(cached_result) = self.cache.get(&text_hash) {
            let mut metrics = self.metrics.write();
            metrics.cache_hits += 1;
            metrics.total_requests += 1;
            
            return ProcessingResult {
                matches: cached_result.matches.clone(),
                processing_time_ns: 0,
                cache_hit: true,
            };
        }
        
        // Process text with zero-copy operations
        let matches = self.find_matches_zero_copy(text);
        
        let processing_time = start_time.elapsed();
        let result = ProcessingResult {
            matches: matches.clone(),
            processing_time_ns: processing_time.as_nanos() as u64,
            cache_hit: false,
        };
        
        // Cache result
        self.cache.insert(text_hash, result.clone());
        
        // Update metrics
        let mut metrics = self.metrics.write();
        metrics.total_requests += 1;
        metrics.total_matches_found += matches.len() as u64;
        metrics.average_processing_time_ns = 
            (metrics.average_processing_time_ns * (metrics.total_requests - 1) + result.processing_time_ns) 
            / metrics.total_requests;
        
        result
    }
    
    /// Find matches using zero-copy operations
    fn find_matches_zero_copy<'a>(&self, text: &'a [u8]) -> Vec<Match> {
        let mut matches = Vec::new();
        
        // Use rayon for parallel pattern matching
        let pattern_matches: Vec<Vec<Match>> = self.patterns
            .par_iter()
            .map(|entry| {
                let pattern_id = *entry.key();
                let pattern = entry.value();
                
                let mut pattern_matches = Vec::new();
                let mut pos = 0;
                
                while let Some(start) = text[pos..].find_pattern(pattern) {
                    let start = pos + start;
                    let end = start + pattern.len();
                    
                    pattern_matches.push(Match {
                        pattern_id,
                        start,
                        end,
                        confidence: 1.0, // Exact match
                    });
                    
                    pos = end;
                }
                
                pattern_matches
            })
            .collect();
        
        // Flatten results
        for pattern_matches in pattern_matches {
            matches.extend(pattern_matches);
        }
        
        // Sort by position
        matches.sort_by_key(|m| m.start);
        matches
    }
    
    /// Batch process multiple texts efficiently
    pub fn process_batch<'a>(&self, texts: &[&'a [u8]]) -> Vec<ProcessingResult> {
        texts.par_iter()
            .map(|text| self.process_text(text))
            .collect()
    }
    
    /// Get processing metrics
    pub fn get_metrics(&self) -> ProcessingMetrics {
        self.metrics.read().clone()
    }
    
    /// Clear cache
    pub fn clear_cache(&self) {
        self.cache.clear();
    }
    
    /// Optimize memory pool
    pub fn optimize_pool(&self) {
        // Remove old buffers to free memory
        for entry in self.pool.buffers.iter() {
            if entry.value().is_empty() {
                entry.remove();
            }
        }
    }
}

/// Zero-copy JSON deserializer for plan parsing
pub struct ZeroCopyPlanParser {
    processor: TextProcessor,
}

impl ZeroCopyPlanParser {
    /// Create new parser
    pub fn new() -> Self {
        Self {
            processor: TextProcessor::new(),
        }
    }
    
    /// Parse plan with zero-copy operations
    pub fn parse_plan<'a>(&self, plan_json: &'a [u8]) -> Result<PlanData<'a>, ParseError> {
        // Use serde_json with zero-copy features
        let plan: PlanData<'a> = serde_json::from_slice(plan_json)
            .map_err(|e| ParseError::JsonParse(e.to_string()))?;
        
        Ok(plan)
    }
}

/// Plan data with zero-copy string references
#[derive(Debug, Deserialize)]
pub struct PlanData<'a> {
    #[serde(borrow)]
    pub plan_id: &'a str,
    #[serde(borrow)]
    pub steps: Vec<PlanStep<'a>>,
    #[serde(borrow)]
    pub metadata: HashMap<&'a str, &'a str>,
}

/// Plan step with zero-copy references
#[derive(Debug, Deserialize)]
pub struct PlanStep<'a> {
    #[serde(borrow)]
    pub tool: &'a str,
    #[serde(borrow)]
    pub args: HashMap<&'a str, &'a str>,
    pub step_index: usize,
}

/// Parse error
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("JSON parse error: {}", .0)]
    JsonParse(String),
    
    #[error("Invalid plan format: {}", .0)]
    InvalidFormat(String),
}

/// Performance profiler for hot-path analysis
pub struct PerformanceProfiler {
    measurements: Arc<RwLock<Vec<Measurement>>>,
    enabled: bool,
}

/// Performance measurement
#[derive(Debug, Clone)]
pub struct Measurement {
    pub operation: String,
    pub duration_ns: u64,
    pub timestamp: Instant,
    pub metadata: HashMap<String, String>,
}

impl PerformanceProfiler {
    /// Create new profiler
    pub fn new(enabled: bool) -> Self {
        Self {
            measurements: Arc::new(RwLock::new(Vec::new())),
            enabled,
        }
    }
    
    /// Measure operation execution time
    pub fn measure<F, R>(&self, operation: &str, f: F) -> R 
    where
        F: FnOnce() -> R,
    {
        if !self.enabled {
            return f();
        }
        
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();
        
        let measurement = Measurement {
            operation: operation.to_string(),
            duration_ns: duration.as_nanos() as u64,
            timestamp: start,
            metadata: HashMap::new(),
        };
        
        self.measurements.write().push(measurement);
        result
    }
    
    /// Get performance summary
    pub fn get_summary(&self) -> PerformanceSummary {
        let measurements = self.measurements.read();
        
        if measurements.is_empty() {
            return PerformanceSummary::default();
        }
        
        let mut operation_stats: HashMap<String, Vec<u64>> = HashMap::new();
        
        for measurement in measurements.iter() {
            operation_stats
                .entry(measurement.operation.clone())
                .or_default()
                .push(measurement.duration_ns);
        }
        
        let mut summary = PerformanceSummary::default();
        
        for (operation, durations) in operation_stats {
            let count = durations.len();
            let total: u64 = durations.iter().sum();
            let avg = total / count as u64;
            
            let mut sorted = durations.clone();
            sorted.sort_unstable();
            let p50 = sorted[count / 2];
            let p95 = sorted[(count * 95) / 100];
            let p99 = sorted[(count * 99) / 100];
            
            summary.operations.insert(operation, OperationStats {
                count,
                total_ns: total,
                average_ns: avg,
                p50_ns: p50,
                p95_ns: p95,
                p99_ns: p99,
            });
        }
        
        summary
    }
    
    /// Clear measurements
    pub fn clear(&self) {
        self.measurements.write().clear();
    }
}

/// Performance summary
#[derive(Debug, Clone, Default)]
pub struct PerformanceSummary {
    pub operations: HashMap<String, OperationStats>,
}

/// Operation statistics
#[derive(Debug, Clone)]
pub struct OperationStats {
    pub count: usize,
    pub total_ns: u64,
    pub average_ns: u64,
    pub p50_ns: u64,
    pub p95_ns: u64,
    pub p99_ns: u64,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_zero_copy_text() {
        let data = b"Hello, World!";
        let text = ZeroCopyText::new(data);
        
        assert_eq!(text.as_bytes(), data);
        assert_eq!(text.as_str(), Some("Hello, World!"));
        assert!(text.contains_pattern(b"World"));
        assert_eq!(text.find_pattern(b"World"), Some(7));
    }
    
    #[test]
    fn test_text_processor() {
        let processor = TextProcessor::new();
        
        // Add patterns
        processor.add_pattern(1, b"hello".to_vec());
        processor.add_pattern(2, b"world".to_vec());
        
        // Process text
        let result = processor.process_text(b"hello world hello");
        
        assert_eq!(result.matches.len(), 3);
        assert_eq!(result.matches[0].pattern_id, 1);
        assert_eq!(result.matches[1].pattern_id, 2);
        assert_eq!(result.matches[2].pattern_id, 1);
    }
    
    #[test]
    fn test_performance_profiler() {
        let profiler = PerformanceProfiler::new(true);
        
        let result = profiler.measure("test_operation", || {
            std::thread::sleep(Duration::from_millis(1));
            42
        });
        
        assert_eq!(result, 42);
        
        let summary = profiler.get_summary();
        assert!(summary.operations.contains_key("test_operation"));
        
        let stats = &summary.operations["test_operation"];
        assert_eq!(stats.count, 1);
        assert!(stats.average_ns > 1_000_000); // Should be > 1ms
    }
}
