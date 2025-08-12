use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};
use serde::{Serialize, Deserialize};
use crate::detectors::{pii, secrets, near_dupe};
use std::collections::VecDeque;

/// Detector pipeline configuration with backpressure controls
#[derive(Debug, Clone)]
pub struct DetectorPipelineConfig {
    pub enable_early_exit: bool,
    pub early_exit_threshold: f64,
    pub max_processing_time_ms: u64,
    pub detector_order: Vec<DetectorType>,
    pub batch_size: usize,
    // Backpressure configuration
    pub enable_backpressure: bool,
    pub max_queue_length: usize,
    pub p95_response_time_budget_ms: u64,
    pub strict_mode_threshold: f64,
    pub critical_detectors: Vec<DetectorType>,
    pub non_critical_detectors: Vec<DetectorType>,
}

impl Default for DetectorPipelineConfig {
    fn default() -> Self {
        Self {
            enable_early_exit: true,
            early_exit_threshold: 0.8,
            max_processing_time_ms: 400, // 400ms target for 2KB payloads
            detector_order: vec![
                DetectorType::AhoCorasick,
                DetectorType::FormatEntropy,
                DetectorType::SimHash64,
                DetectorType::MinHashLSH,
                DetectorType::NLP,
            ],
            batch_size: 64,
            // Backpressure defaults
            enable_backpressure: true,
            max_queue_length: 1000,
            p95_response_time_budget_ms: 500,
            strict_mode_threshold: 0.8,
            critical_detectors: vec![
                DetectorType::AhoCorasick,
                DetectorType::FormatEntropy,
            ],
            non_critical_detectors: vec![
                DetectorType::SimHash64,
                DetectorType::MinHashLSH,
                DetectorType::NLP,
            ],
        }
    }
}

/// Detector types in order of execution
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DetectorType {
    AhoCorasick,   // Fast dictionary-based detection
    FormatEntropy, // Format and entropy analysis
    SimHash64,     // Fast similarity hashing
    MinHashLSH,    // Locality-sensitive hashing
    NLP,           // Heavy NLP processing
}

impl std::fmt::Display for DetectorType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DetectorType::AhoCorasick => write!(f, "aho_corasick"),
            DetectorType::FormatEntropy => write!(f, "format_entropy"),
            DetectorType::SimHash64 => write!(f, "simhash64"),
            DetectorType::MinHashLSH => write!(f, "minhash_lsh"),
            DetectorType::NLP => write!(f, "nlp"),
        }
    }
}

/// Pipeline execution result with backpressure information
#[derive(Debug, Clone)]
pub struct PipelineResult {
    pub detector_results: DetectorResults,
    pub early_exit: bool,
    pub exit_reason: Option<String>,
    pub processing_time_ms: u64,
    pub detector_timings: HashMap<DetectorType, u64>,
    pub cache_hit: bool,
    // Backpressure information
    pub strict_mode_active: bool,
    pub strict_mode_reason: Option<String>,
    pub detectors_skipped: Vec<DetectorType>,
}

/// Detector results structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorResults {
    pub pii_detected: bool,
    pub secrets_detected: bool,
    pub near_dupe_detected: bool,
    pub policy_violations: Vec<String>,
    pub confidence_scores: HashMap<String, f64>,
    pub critical_hits: Vec<String>,
}

/// Backpressure state for the pipeline
#[derive(Debug, Clone)]
pub struct BackpressureState {
    pub strict_mode_active: bool,
    pub strict_mode_reason: Option<String>,
    pub strict_mode_activated_at: Option<Instant>,
    pub current_queue_length: usize,
    pub p95_response_time_ms: u64,
    pub total_requests: u64,
    pub dropped_requests: u64,
    pub critical_leaks: u64,
}

impl Default for BackpressureState {
    fn default() -> Self {
        Self {
            strict_mode_active: false,
            strict_mode_reason: None,
            strict_mode_activated_at: None,
            current_queue_length: 0,
            p95_response_time_ms: 0,
            total_requests: 0,
            dropped_requests: 0,
            critical_leaks: 0,
        }
    }
}

/// Pipeline request with priority and metadata
#[derive(Debug, Clone)]
pub struct PipelineRequest {
    pub id: String,
    pub priority: RequestPriority,
    pub detector_types: Vec<DetectorType>,
    pub created_at: Instant,
    pub tenant: String,
    pub payload_size: usize,
}

/// Request priority levels
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum RequestPriority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// Pipeline operation errors
#[derive(Debug, thiserror::Error)]
pub enum PipelineError {
    #[error("Queue is full: current length {current_length}, max length {max_length}")]
    QueueFull { current_length: usize, max_length: usize },
    
    #[error("Processing timeout: exceeded {}ms", .0)]
    ProcessingTimeout(u64),
    
    #[error("Detector error: {}", .0)]
    DetectorError(String),
}

/// Streaming detector pipeline with backpressure control
pub struct DetectorPipeline {
    config: DetectorPipelineConfig,
    cache: Arc<RwLock<HashMap<String, CachedResult>>>,
    metrics: Arc<RwLock<PipelineMetrics>>,
    pii_detector: Arc<pii::PiiDetector>,
    secrets_detector: Arc<secrets::SecretsDetector>,
    near_dupe_detector: Arc<near_dupe::NearDupeDetector>,
    // Backpressure components
    backpressure_state: Arc<RwLock<BackpressureState>>,
    response_times: Arc<RwLock<Vec<u64>>>,
    request_queue: Arc<RwLock<VecDeque<PipelineRequest>>>,
}

/// Cached detection result
#[derive(Debug, Clone)]
struct CachedResult {
    result: DetectorResults,
    created_at: Instant,
    ttl: Duration,
}

/// Pipeline performance metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PipelineMetrics {
    pub total_scans: u64,
    pub early_exits: u64,
    pub cache_hits: u64,
    pub average_processing_time_ms: u64,
    pub detector_performance: HashMap<DetectorType, DetectorMetrics>,
}

/// Individual detector metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DetectorMetrics {
    pub total_runs: u64,
    pub average_time_ms: u64,
    pub early_exit_triggers: u64,
    pub false_positive_rate: f64,
}

impl DetectorPipeline {
    /// Create a new detector pipeline
    pub fn new(config: DetectorPipelineConfig) -> Self {
        Self {
            config,
            cache: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(PipelineMetrics::default())),
            pii_detector: Arc::new(pii::PiiDetector::new()),
            secrets_detector: Arc::new(secrets::SecretsDetector::new()),
            near_dupe_detector: Arc::new(near_dupe::NearDupeDetector::new()),
            // Backpressure components
            backpressure_state: Arc::new(RwLock::new(BackpressureState::default())),
            response_times: Arc::new(RwLock::new(Vec::new())),
            request_queue: Arc::new(RwLock::new(VecDeque::new())),
        }
    }

    /// Process text through the detector pipeline
    pub async fn process_text(&self, text: &str, context: &HashMap<String, String>) -> PipelineResult {
        let start_time = Instant::now();
        
        // Check cache first
        let cache_key = self.generate_cache_key(text, context);
        if let Some(cached) = self.get_from_cache(&cache_key).await {
            self.update_metrics(true, start_time.elapsed(), false).await;
            return PipelineResult {
                detector_results: cached.result,
                early_exit: false,
                exit_reason: Some("cache_hit".to_string()),
                processing_time_ms: 0,
                detector_timings: HashMap::new(),
                cache_hit: true,
                strict_mode_active: false,
                strict_mode_reason: None,
                detectors_skipped: vec![],
            };
        }

        // Execute detector pipeline
        let result = self.execute_pipeline(text, context, start_time).await;
        
        // Cache the result
        self.cache_result(&cache_key, &result.detector_results).await;
        
        // Update metrics
        self.update_metrics(false, start_time.elapsed(), result.early_exit).await;
        
        result
    }

    /// Execute the detector pipeline with early exit capability and backpressure control
    async fn execute_pipeline(
        &self,
        text: &str,
        context: &HashMap<String, String>,
        start_time: Instant,
    ) -> PipelineResult {
        let mut detector_timings = HashMap::new();
        let mut results = DetectorResults::default();
        let mut early_exit = false;
        let mut exit_reason = None;
        let mut detectors_skipped = Vec::new();

        // Check backpressure state before execution
        let strict_mode_active = self.check_backpressure_state().await;
        let strict_mode_reason = if strict_mode_active {
            self.get_strict_mode_reason().await
        } else {
            None
        };

        // Execute detectors in order with backpressure control
        for detector_type in &self.config.detector_order {
            // Skip non-critical detectors in strict mode
            if strict_mode_active && self.is_non_critical_detector(detector_type) {
                detectors_skipped.push(*detector_type);
                continue;
            }

            let detector_start = Instant::now();
            
            let detector_result = match detector_type {
                DetectorType::AhoCorasick => {
                    self.run_aho_corasick_detector(text, context).await
                }
                DetectorType::FormatEntropy => {
                    self.run_format_entropy_detector(text, context).await
                }
                DetectorType::SimHash64 => {
                    self.run_simhash_detector(text, context).await
                }
                DetectorType::MinHashLSH => {
                    self.run_minhash_detector(text, context).await
                }
                DetectorType::NLP => {
                    self.run_nlp_detector(text, context).await
                }
            };

            let detector_time = detector_start.elapsed();
            detector_timings.insert(*detector_type, detector_time.as_millis() as u64);

            // Merge results
            self.merge_detector_results(&mut results, detector_result);

            // Check for early exit conditions
            if self.config.enable_early_exit && self.should_early_exit(&results, detector_type) {
                early_exit = true;
                exit_reason = Some(format!("early_exit_at_{}", detector_type));
                break;
            }

            // Check processing time limit
            if start_time.elapsed().as_millis() as u64 > self.config.max_processing_time_ms {
                early_exit = true;
                exit_reason = Some("timeout".to_string());
                break;
            }
        }

        // Record response time for backpressure monitoring
        let response_time = start_time.elapsed().as_millis() as u64;
        self.record_response_time(response_time).await;

        PipelineResult {
            detector_results: results,
            early_exit,
            exit_reason,
            processing_time_ms: response_time,
            detector_timings,
            cache_hit: false,
            strict_mode_active,
            strict_mode_reason,
            detectors_skipped,
        }
    }

    /// Run Aho-Corasick dictionary-based detector
    async fn run_aho_corasick_detector(
        &self,
        text: &str,
        _context: &HashMap<String, String>,
    ) -> DetectorResults {
        // This would integrate with the actual PII detector
        let pii_result = self.pii_detector.detect_fast(text).await;
        
        DetectorResults {
            pii_detected: pii_result.detected,
            secrets_detected: false,
            near_dupe_detected: false,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: if pii_result.detected { vec!["pii".to_string()] } else { vec![] },
        }
    }

    /// Run format and entropy analysis detector
    async fn run_format_entropy_detector(
        &self,
        text: &str,
        _context: &HashMap<String, String>,
    ) -> DetectorResults {
        // Analyze text format and entropy patterns
        let secrets_result = self.secrets_detector.detect_format_entropy(text).await;
        
        DetectorResults {
            pii_detected: false,
            secrets_detected: secrets_result.detected,
            near_dupe_detected: false,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: if secrets_result.detected { vec!["secrets".to_string()] } else { vec![] },
        }
    }

    /// Run SimHash64 similarity detector
    async fn run_simhash_detector(
        &self,
        text: &str,
        _context: &HashMap<String, String>,
    ) -> DetectorResults {
        // Fast similarity detection using SimHash
        let near_dupe_result = self.near_dupe_detector.detect_simhash(text).await;
        
        DetectorResults {
            pii_detected: false,
            secrets_detected: false,
            near_dupe_detected: near_dupe_result.is_duplicate,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: vec![],
        }
    }

    /// Run MinHash LSH detector
    async fn run_minhash_detector(
        &self,
        text: &str,
        _context: &HashMap<String, String>,
    ) -> DetectorResults {
        // Locality-sensitive hashing for near-duplicate detection
        let near_dupe_result = self.near_dupe_detector.detect_minhash(text).await;
        
        DetectorResults {
            pii_detected: false,
            secrets_detected: false,
            near_dupe_detected: near_dupe_result.is_duplicate,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: vec![],
        }
    }

    /// Run NLP-based detector (heavy processing)
    async fn run_nlp_detector(
        &self,
        text: &str,
        _context: &HashMap<String, String>,
    ) -> DetectorResults {
        // Heavy NLP processing for ambiguous cases
        let pii_result = self.pii_detector.detect_nlp(text).await;
        let secrets_result = self.secrets_detector.detect_nlp(text).await;
        
        DetectorResults {
            pii_detected: pii_result.detected,
            secrets_detected: secrets_result.detected,
            near_dupe_detected: false,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: vec![],
        }
    }

    /// Check if early exit should be triggered
    fn should_early_exit(&self, results: &DetectorResults, detector_type: &DetectorType) -> bool {
        // Early exit on critical hits
        if !results.critical_hits.is_empty() {
            return true;
        }

        // Early exit on high confidence detections
        for (_, confidence) in &results.confidence_scores {
            if *confidence >= self.config.early_exit_threshold {
                return true;
            }
        }

        // Early exit after SimHash if no issues found
        if *detector_type == DetectorType::SimHash64 && 
           !results.pii_detected && 
           !results.secrets_detected && 
           !results.near_dupe_detected {
            return true;
        }

        false
    }

    /// Merge detector results
    fn merge_detector_results(&self, base: &mut DetectorResults, new: DetectorResults) {
        base.pii_detected |= new.pii_detected;
        base.secrets_detected |= new.secrets_detected;
        base.near_dupe_detected |= new.near_dupe_detected;
        base.policy_violations.extend(new.policy_violations);
        base.critical_hits.extend(new.critical_hits);
        
        for (key, value) in new.confidence_scores {
            base.confidence_scores.insert(key, value);
        }
    }

    /// Generate cache key for text and context
    fn generate_cache_key(&self, text: &str, context: &HashMap<String, String>) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(text.as_bytes());
        
        // Include relevant context in cache key
        let mut context_vec: Vec<_> = context.iter().collect();
        context_vec.sort_by_key(|(k, _)| *k);
        for (k, v) in context_vec {
            hasher.update(k.as_bytes());
            hasher.update(v.as_bytes());
        }
        
        hex::encode(hasher.finalize())
    }

    /// Get result from cache
    async fn get_from_cache(&self, key: &str) -> Option<CachedResult> {
        let cache = self.cache.read().await;
        if let Some(cached) = cache.get(key) {
            if cached.created_at.elapsed() < cached.ttl {
                return Some(cached.clone());
            }
        }
        None
    }

    /// Cache detection result
    async fn cache_result(&self, key: &str, result: &DetectorResults) {
        let mut cache = self.cache.write().await;
        let cached = CachedResult {
            result: result.clone(),
            created_at: Instant::now(),
            ttl: Duration::from_secs(300), // 5 minutes TTL
        };
        cache.insert(key.to_string(), cached);
    }

    /// Update pipeline metrics
    async fn update_metrics(&self, cache_hit: bool, processing_time: Duration, early_exit: bool) {
        let mut metrics = self.metrics.write().await;
        
        metrics.total_scans += 1;
        if cache_hit {
            metrics.cache_hits += 1;
        }
        if early_exit {
            metrics.early_exits += 1;
        }
        
        let time_ms = processing_time.as_millis() as u64;
        metrics.average_processing_time_ms = 
            (metrics.average_processing_time_ms * (metrics.total_scans - 1) + time_ms) / metrics.total_scans;
    }

    /// Get pipeline metrics
    pub async fn get_metrics(&self) -> PipelineMetrics {
        self.metrics.read().await.clone()
    }

    /// Clear pipeline cache
    pub async fn clear_cache(&self) {
        let mut cache = self.cache.write().await;
        cache.clear();
    }

    /// Update detector performance metrics
    pub async fn update_detector_metrics(&self, detector_type: DetectorType, time_ms: u64, early_exit: bool) {
        let mut metrics = self.metrics.write().await;
        let detector_metrics = metrics.detector_performance.entry(detector_type).or_insert_with(DetectorMetrics::default);
        
        detector_metrics.total_runs += 1;
        detector_metrics.average_time_ms = 
            (detector_metrics.average_time_ms * (detector_metrics.total_runs - 1) + time_ms) / detector_metrics.total_runs;
        
        if early_exit {
            detector_metrics.early_exit_triggers += 1;
        }
    }

    /// Check backpressure state and activate strict mode if needed
    async fn check_backpressure_state(&self) -> bool {
        if !self.config.enable_backpressure {
            return false;
        }

        let mut state = self.backpressure_state.write().await;
        
        // Check queue length threshold
        let queue_length = self.request_queue.read().await.len();
        let queue_threshold = (self.config.max_queue_length as f64 * self.config.strict_mode_threshold) as usize;
        
        if queue_length >= queue_threshold {
            if !state.strict_mode_active {
                state.strict_mode_active = true;
                state.strict_mode_reason = Some(format!(
                    "queue_length_exceeded: {} >= {}",
                    queue_length, queue_threshold
                ));
                state.strict_mode_activated_at = Some(Instant::now());
                
                tracing::warn!(
                    "Strict mode activated: queue length {} exceeds threshold {}",
                    queue_length, queue_threshold
                );
            }
            return true;
        }

        // Check p95 response time budget
        let p95_response_time = self.calculate_p95_response_time().await;
        if p95_response_time > self.config.p95_response_time_budget_ms {
            if !state.strict_mode_active {
                state.strict_mode_active = true;
                state.strict_mode_reason = Some(format!(
                    "p95_response_time_breached: {}ms > {}ms",
                    p95_response_time, self.config.p95_response_time_budget_ms
                ));
                state.strict_mode_activated_at = Some(Instant::now());
                
                tracing::warn!(
                    "Strict mode activated: p95 response time {}ms exceeds budget {}ms",
                    p95_response_time, self.config.p95_response_time_budget_ms
                );
            }
            return true;
        }

        // Deactivate strict mode if conditions have improved
        if state.strict_mode_active {
            let cooldown_duration = Duration::from_secs(30); // 30 second cooldown
            if let Some(activated_at) = state.strict_mode_activated_at {
                if activated_at.elapsed() >= cooldown_duration {
                    let queue_ok = queue_length < (self.config.max_queue_length as f64 * 0.6) as usize;
                    let response_time_ok = p95_response_time < self.config.p95_response_time_budget_ms;
                    
                    if queue_ok && response_time_ok {
                        state.strict_mode_active = false;
                        state.strict_mode_reason = None;
                        state.strict_mode_activated_at = None;
                        
                        tracing::info!(
                            "Strict mode deactivated: queue length {}, p95 response time {}ms",
                            queue_length, p95_response_time
                        );
                    }
                }
            }
        }

        state.strict_mode_active
    }

    /// Get current strict mode reason
    async fn get_strict_mode_reason(&self) -> Option<String> {
        self.backpressure_state.read().await.strict_mode_reason.clone()
    }

    /// Check if a detector type is non-critical
    fn is_non_critical_detector(&self, detector_type: &DetectorType) -> bool {
        self.config.non_critical_detectors.contains(detector_type)
    }

    /// Record response time for backpressure monitoring
    async fn record_response_time(&self, time_ms: u64) {
        let mut response_times = self.response_times.write().await;
        response_times.push(time_ms);
        
        // Keep only recent response times (last 1000)
        if response_times.len() > 1000 {
            response_times.remove(0);
        }
    }

    /// Calculate p95 response time
    async fn calculate_p95_response_time(&self) -> u64 {
        let response_times = self.response_times.read().await;
        
        if response_times.is_empty() {
            return 0;
        }
        
        let mut sorted_times = response_times.clone();
        sorted_times.sort_unstable();
        
        let p95_idx = (sorted_times.len() as f64 * 0.95) as usize;
        sorted_times.get(p95_idx).copied().unwrap_or(0)
    }

    /// Submit a request to the pipeline with backpressure control
    pub async fn submit_request(&self, request: PipelineRequest) -> Result<(), PipelineError> {
        if !self.config.enable_backpressure {
            return Ok(());
        }

        let mut queue = self.request_queue.write().await;
        
        // Check queue length limits
        if queue.len() >= self.config.max_queue_length {
            let mut state = self.backpressure_state.write().await;
            state.dropped_requests += 1;
            
            tracing::error!(
                "Pipeline queue full, dropping request: {} (queue length: {})",
                request.id, queue.len()
            );
            
            return Err(PipelineError::QueueFull {
                current_length: queue.len(),
                max_length: self.config.max_queue_length,
            });
        }
        
        // Enqueue request
        queue.push_back(request);
        
        // Update backpressure state
        let mut state = self.backpressure_state.write().await;
        state.current_queue_length = queue.len();
        state.total_requests += 1;
        
        Ok(())
    }

    /// Get backpressure state
    pub async fn get_backpressure_state(&self) -> BackpressureState {
        self.backpressure_state.read().await.clone()
    }

    /// Manually activate strict mode
    pub async fn activate_strict_mode(&self, reason: String) {
        let mut state = self.backpressure_state.write().await;
        state.strict_mode_active = true;
        state.strict_mode_reason = Some(reason);
        state.strict_mode_activated_at = Some(Instant::now());
        
        tracing::info!("Strict mode manually activated");
    }

    /// Manually deactivate strict mode
    pub async fn deactivate_strict_mode(&self) {
        let mut state = self.backpressure_state.write().await;
        state.strict_mode_active = false;
        state.strict_mode_reason = None;
        state.strict_mode_activated_at = None;
        
        tracing::info!("Strict mode manually deactivated");
    }
}

impl Default for DetectorResults {
    fn default() -> Self {
        Self {
            pii_detected: false,
            secrets_detected: false,
            near_dupe_detected: false,
            policy_violations: vec![],
            confidence_scores: HashMap::new(),
            critical_hits: vec![],
        }
    }
}

impl Default for PipelineMetrics {
    fn default() -> Self {
        Self {
            total_scans: 0,
            early_exits: 0,
            cache_hits: 0,
            average_processing_time_ms: 0,
            detector_performance: HashMap::new(),
        }
    }
}

impl Default for DetectorMetrics {
    fn default() -> Self {
        Self {
            total_runs: 0,
            average_time_ms: 0,
            early_exit_triggers: 0,
            false_positive_rate: 0.0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_pipeline_creation() {
        let config = DetectorPipelineConfig::default();
        let pipeline = DetectorPipeline::new(config);
        assert!(pipeline.config.enable_early_exit);
        assert!(pipeline.config.enable_backpressure);
    }

    #[tokio::test]
    async fn test_early_exit_logic() {
        let config = DetectorPipelineConfig::default();
        let pipeline = DetectorPipeline::new(config);
        
        let mut results = DetectorResults::default();
        results.critical_hits.push("pii".to_string());
        
        let should_exit = pipeline.should_early_exit(&results, &DetectorType::AhoCorasick);
        assert!(should_exit);
    }

    #[tokio::test]
    async fn test_cache_functionality() {
        let config = DetectorPipelineConfig::default();
        let pipeline = DetectorPipeline::new(config);
        
        let context = HashMap::new();
        let text = "test text for caching";
        
        // First run should miss cache
        let result1 = pipeline.process_text(text, &context).await;
        assert!(!result1.cache_hit);
        
        // Second run should hit cache
        let result2 = pipeline.process_text(text, &context).await;
        assert!(result2.cache_hit);
    }

    #[tokio::test]
    async fn test_backpressure_strict_mode() {
        let mut config = DetectorPipelineConfig::default();
        config.max_queue_length = 10;
        config.strict_mode_threshold = 0.5; // 50%
        
        let pipeline = DetectorPipeline::new(config);
        
        // Fill queue to trigger strict mode
        for i in 0..6 {
            let request = PipelineRequest {
                id: format!("test-{}", i),
                priority: RequestPriority::Normal,
                detector_types: vec![DetectorType::AhoCorasick],
                created_at: Instant::now(),
                tenant: "test-tenant".to_string(),
                payload_size: 1024,
            };
            pipeline.submit_request(request).await.unwrap();
        }
        
        // Wait for backpressure state update
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let backpressure_state = pipeline.get_backpressure_state().await;
        assert!(backpressure_state.strict_mode_active);
        assert!(backpressure_state.strict_mode_reason.is_some());
    }

    #[tokio::test]
    async fn test_non_critical_detector_skipping() {
        let mut config = DetectorPipelineConfig::default();
        config.max_queue_length = 10;
        config.strict_mode_threshold = 0.5;
        
        let pipeline = DetectorPipeline::new(config);
        
        // Fill queue to trigger strict mode
        for i in 0..6 {
            let request = PipelineRequest {
                id: format!("test-{}", i),
                priority: RequestPriority::Normal,
                detector_types: vec![DetectorType::AhoCorasick],
                created_at: Instant::now(),
                tenant: "test-tenant".to_string(),
                payload_size: 1024,
            };
            pipeline.submit_request(request).await.unwrap();
        }
        
        // Wait for backpressure state update
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        // Process text - should skip non-critical detectors
        let context = HashMap::new();
        let text = "test text with PII data";
        
        let result = pipeline.process_text(text, &context).await;
        assert!(result.strict_mode_active);
        assert!(!result.detectors_skipped.is_empty());
        
        // Verify that non-critical detectors were skipped
        let skipped_detectors: Vec<_> = result.detectors_skipped.iter().collect();
        assert!(skipped_detectors.contains(&&DetectorType::NLP));
        assert!(skipped_detectors.contains(&&DetectorType::MinHashLSH));
    }

    #[tokio::test]
    async fn test_manual_strict_mode_control() {
        let config = DetectorPipelineConfig::default();
        let pipeline = DetectorPipeline::new(config);
        
        // Manually activate strict mode
        pipeline.activate_strict_mode("manual_test".to_string()).await;
        
        let backpressure_state = pipeline.get_backpressure_state().await;
        assert!(backpressure_state.strict_mode_active);
        assert_eq!(backpressure_state.strict_mode_reason, Some("manual_test".to_string()));
        
        // Manually deactivate strict mode
        pipeline.deactivate_strict_mode().await;
        
        let backpressure_state = pipeline.get_backpressure_state().await;
        assert!(!backpressure_state.strict_mode_active);
        assert!(backpressure_state.strict_mode_reason.is_none());
    }
}
