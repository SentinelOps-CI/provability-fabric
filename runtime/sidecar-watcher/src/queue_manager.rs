use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::timeout;
use tracing::{info, warn, error, instrument};
use serde::{Serialize, Deserialize};
use metrics::{counter, gauge, histogram};

/// Queue manager configuration
#[derive(Debug, Clone)]
pub struct QueueManagerConfig {
    /// Maximum queue length before strict mode activation
    pub max_queue_length: usize,
    /// P95 response time budget in milliseconds
    pub p95_response_time_budget_ms: u64,
    /// Strict mode activation threshold (queue length percentage)
    pub strict_mode_threshold: f64,
    /// Critical detector types that should never be dropped
    pub critical_detectors: Vec<String>,
    /// Non-critical detector types that can be dropped in strict mode
    pub non_critical_detectors: Vec<String>,
    /// Monitoring window size for p95 calculations
    pub monitoring_window_size: usize,
    /// Strict mode cooldown period
    pub strict_mode_cooldown_ms: u64,
}

impl Default for QueueManagerConfig {
    fn default() -> Self {
        Self {
            max_queue_length: 1000,
            p95_response_time_budget_ms: 500,
            strict_mode_threshold: 0.8,
            critical_detectors: vec![
                "pii_detector".to_string(),
                "secrets_detector".to_string(),
                "policy_enforcement".to_string(),
            ],
            non_critical_detectors: vec![
                "near_dupe_detector".to_string(),
                "nlp_detector".to_string(),
                "format_entropy_detector".to_string(),
            ],
            monitoring_window_size: 1000,
            strict_mode_cooldown_ms: 30000, // 30 seconds
        }
    }
}

/// Queue item with priority and metadata
#[derive(Debug, Clone)]
pub struct QueueItem {
    pub id: String,
    pub priority: Priority,
    pub detector_type: String,
    pub created_at: Instant,
    pub tenant: String,
    pub payload_size: usize,
}

/// Priority levels for queue items
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Priority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// Strict mode activation reason
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StrictModeReason {
    QueueLengthExceeded { current: usize, threshold: usize },
    P95ResponseTimeBreached { current: u64, budget: u64 },
    ManualActivation { reason: String },
}

/// Queue manager state
#[derive(Debug, Clone)]
pub struct QueueManagerState {
    pub strict_mode_active: bool,
    pub strict_mode_reason: Option<StrictModeReason>,
    pub strict_mode_activated_at: Option<Instant>,
    pub current_queue_length: usize,
    pub p95_response_time_ms: u64,
    pub total_requests: u64,
    pub dropped_requests: u64,
    pub critical_leaks: u64,
}

/// Queue manager for backpressure and load-shedding
pub struct QueueManager {
    config: QueueManagerConfig,
    queue: Arc<RwLock<VecDeque<QueueItem>>>,
    semaphore: Arc<Semaphore>,
    state: Arc<RwLock<QueueManagerState>>,
    response_times: Arc<RwLock<Vec<u64>>>,
    metrics: Arc<RwLock<QueueMetrics>>,
}

/// Queue performance metrics
#[derive(Debug, Clone, Default)]
pub struct QueueMetrics {
    pub total_enqueued: u64,
    pub total_dequeued: u64,
    pub total_dropped: u64,
    pub strict_mode_activations: u64,
    pub strict_mode_duration_ms: u64,
    pub average_queue_length: f64,
    pub p95_response_time_ms: u64,
    pub p99_response_time_ms: u64,
}

impl QueueManager {
    /// Create a new queue manager
    pub fn new(config: QueueManagerConfig) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_queue_length));
        
        Self {
            config,
            queue: Arc::new(RwLock::new(VecDeque::new())),
            semaphore,
            state: Arc::new(RwLock::new(QueueManagerState {
                strict_mode_active: false,
                strict_mode_reason: None,
                strict_mode_activated_at: None,
                current_queue_length: 0,
                p95_response_time_ms: 0,
                total_requests: 0,
                dropped_requests: 0,
                critical_leaks: 0,
            })),
            response_times: Arc::new(RwLock::new(Vec::new())),
            metrics: Arc::new(RwLock::new(QueueMetrics::default())),
        }
    }

    /// Enqueue an item with backpressure control
    #[instrument(skip(self, item), fields(item_id = %item.id, detector_type = %item.detector_type))]
    pub async fn enqueue(&self, item: QueueItem) -> Result<(), QueueError> {
        let mut state = self.state.write().await;
        
        // Check if we should activate strict mode
        self.check_strict_mode_activation(&mut state).await;
        
        // In strict mode, drop non-critical items
        if state.strict_mode_active && self.should_drop_item(&item) {
            state.dropped_requests += 1;
            self.update_metrics_drop().await;
            
            warn!(
                "Dropping non-critical request in strict mode: {} (detector: {})",
                item.id, item.detector_type
            );
            
            return Err(QueueError::ItemDropped {
                reason: "strict_mode_active".to_string(),
                detector_type: item.detector_type.clone(),
            });
        }
        
        // Check queue length limits
        if self.queue.read().await.len() >= self.config.max_queue_length {
            state.dropped_requests += 1;
            self.update_metrics_drop().await;
            
            error!(
                "Queue full, dropping request: {} (queue length: {})",
                item.id, self.queue.read().await.len()
            );
            
            return Err(QueueError::QueueFull {
                current_length: self.queue.read().await.len(),
                max_length: self.config.max_queue_length,
            });
        }
        
        // Acquire semaphore permit
        let _permit = self.semaphore.acquire().await.map_err(|_| {
            QueueError::SemaphoreAcquisitionFailed
        })?;
        
        // Enqueue item
        let mut queue = self.queue.write().await;
        queue.push_back(item.clone());
        state.current_queue_length = queue.len();
        state.total_requests += 1;
        
        // Update metrics
        self.update_metrics_enqueue().await;
        
        info!(
            "Enqueued request: {} (detector: {}, priority: {:?}, queue length: {})",
            item.id, item.detector_type, item.priority, queue.len()
        );
        
        Ok(())
    }

    /// Dequeue an item with priority ordering
    #[instrument(skip(self))]
    pub async fn dequeue(&self, timeout: Duration) -> Result<Option<QueueItem>, QueueError> {
        let start_time = Instant::now();
        
        // Wait for item with timeout
        let item = timeout(timeout, self.wait_for_item()).await.map_err(|_| {
            QueueError::DequeueTimeout
        })?;
        
        if let Some(item) = item {
            let processing_time = start_time.elapsed();
            
            // Record response time
            self.record_response_time(processing_time.as_millis() as u64).await;
            
            // Update state
            let mut state = self.state.write().await;
            state.current_queue_length = self.queue.read().await.len();
            
            // Update metrics
            self.update_metrics_dequeue().await;
            
            // Check if we should deactivate strict mode
            self.check_strict_mode_deactivation(&mut state).await;
            
            info!(
                "Dequeued request: {} (detector: {}, processing time: {:?})",
                item.id, item.detector_type, processing_time
            );
        }
        
        Ok(item)
    }

    /// Wait for an item to become available
    async fn wait_for_item(&self) -> Option<QueueItem> {
        loop {
            let mut queue = self.queue.write().await;
            
            if let Some(item) = self.dequeue_highest_priority(&mut queue) {
                return Some(item);
            }
            
            // Release lock and wait
            drop(queue);
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    /// Dequeue highest priority item
    fn dequeue_highest_priority(&self, queue: &mut VecDeque<QueueItem>) -> Option<QueueItem> {
        if queue.is_empty() {
            return None;
        }
        
        // Find highest priority item
        let mut highest_priority_idx = 0;
        let mut highest_priority = &queue[0].priority;
        
        for (idx, item) in queue.iter().enumerate() {
            if item.priority > *highest_priority {
                highest_priority = &item.priority;
                highest_priority_idx = idx;
            }
        }
        
        // Remove and return highest priority item
        queue.remove(highest_priority_idx)
    }

    /// Check if strict mode should be activated
    async fn check_strict_mode_activation(&self, state: &mut QueueManagerState) {
        if state.strict_mode_active {
            return; // Already active
        }
        
        let queue_length = self.queue.read().await.len();
        let p95_response_time = self.calculate_p95_response_time().await;
        
        // Check queue length threshold
        if queue_length as f64 >= self.config.max_queue_length as f64 * self.config.strict_mode_threshold {
            state.strict_mode_active = true;
            state.strict_mode_reason = Some(StrictModeReason::QueueLengthExceeded {
                current: queue_length,
                threshold: (self.config.max_queue_length as f64 * self.config.strict_mode_threshold) as usize,
            });
            state.strict_mode_activated_at = Some(Instant::now());
            
            warn!(
                "Strict mode activated: queue length {} exceeds threshold {}",
                queue_length, self.config.max_queue_length
            );
            
            self.activate_strict_mode_metrics().await;
        }
        
        // Check p95 response time budget
        if p95_response_time > self.config.p95_response_time_budget_ms {
            state.strict_mode_active = true;
            state.strict_mode_reason = Some(StrictModeReason::P95ResponseTimeBreached {
                current: p95_response_time,
                budget: self.config.p95_response_time_budget_ms,
            });
            state.strict_mode_activated_at = Some(Instant::now());
            
            warn!(
                "Strict mode activated: p95 response time {}ms exceeds budget {}ms",
                p95_response_time, self.config.p95_response_time_budget_ms
            );
            
            self.activate_strict_mode_metrics().await;
        }
    }

    /// Check if strict mode should be deactivated
    async fn check_strict_mode_deactivation(&self, state: &mut QueueManagerState) {
        if !state.strict_mode_active {
            return;
        }
        
        if let Some(activated_at) = state.strict_mode_activated_at {
            let cooldown_duration = Duration::from_millis(self.config.strict_mode_cooldown_ms);
            
            if activated_at.elapsed() >= cooldown_duration {
                let queue_length = self.queue.read().await.len();
                let p95_response_time = self.calculate_p95_response_time().await;
                
                // Check if conditions have improved
                let queue_ok = queue_length < (self.config.max_queue_length as f64 * 0.6) as usize;
                let response_time_ok = p95_response_time < self.config.p95_response_time_budget_ms;
                
                if queue_ok && response_time_ok {
                    state.strict_mode_active = false;
                    state.strict_mode_reason = None;
                    state.strict_mode_activated_at = None;
                    
                    info!(
                        "Strict mode deactivated: queue length {}, p95 response time {}ms",
                        queue_length, p95_response_time
                    );
                    
                    self.deactivate_strict_mode_metrics().await;
                }
            }
        }
    }

    /// Check if an item should be dropped in strict mode
    fn should_drop_item(&self, item: &QueueItem) -> bool {
        // Never drop critical priority items
        if item.priority == Priority::Critical {
            return false;
        }
        
        // Drop non-critical detector types
        self.config.non_critical_detectors.contains(&item.detector_type)
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

    /// Record response time for monitoring
    async fn record_response_time(&self, time_ms: u64) {
        let mut response_times = self.response_times.write().await;
        response_times.push(time_ms);
        
        // Keep only recent response times
        if response_times.len() > self.config.monitoring_window_size {
            response_times.remove(0);
        }
        
        // Update p95 in state
        let p95 = self.calculate_p95_response_time().await;
        let mut state = self.state.write().await;
        state.p95_response_time_ms = p95;
    }

    /// Update metrics for enqueue
    async fn update_metrics_enqueue(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.total_enqueued += 1;
        
        let queue_length = self.queue.read().await.len();
        metrics.average_queue_length = 
            (metrics.average_queue_length * (metrics.total_enqueued - 1) as f64 + queue_length as f64) 
            / metrics.total_enqueued as f64;
        
        // Update Prometheus metrics
        counter!("queue_enqueued_total", 1);
        gauge!("queue_length_current", queue_length as f64);
        gauge!("queue_length_average", metrics.average_queue_length);
    }

    /// Update metrics for dequeue
    async fn update_metrics_dequeue(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.total_dequeued += 1;
        
        // Update Prometheus metrics
        counter!("queue_dequeued_total", 1);
    }

    /// Update metrics for dropped items
    async fn update_metrics_drop(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.total_dropped += 1;
        
        // Update Prometheus metrics
        counter!("queue_dropped_total", 1);
    }

    /// Activate strict mode metrics
    async fn activate_strict_mode_metrics(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.strict_mode_activations += 1;
        
        // Update Prometheus metrics
        counter!("strict_mode_activations_total", 1);
        gauge!("strict_mode_active", 1.0);
    }

    /// Deactivate strict mode metrics
    async fn deactivate_strict_mode_metrics(&self) {
        // Update Prometheus metrics
        gauge!("strict_mode_active", 0.0);
    }

    /// Get current queue manager state
    pub async fn get_state(&self) -> QueueManagerState {
        self.state.read().await.clone()
    }

    /// Get queue metrics
    pub async fn get_metrics(&self) -> QueueMetrics {
        self.metrics.read().await.clone()
    }

    /// Manually activate strict mode
    pub async fn activate_strict_mode(&self, reason: String) {
        let mut state = self.state.write().await;
        state.strict_mode_active = true;
        state.strict_mode_reason = Some(StrictModeReason::ManualActivation { reason });
        state.strict_mode_activated_at = Some(Instant::now());
        
        info!("Strict mode manually activated: {}", reason);
        self.activate_strict_mode_metrics().await;
    }

    /// Manually deactivate strict mode
    pub async fn deactivate_strict_mode(&self) {
        let mut state = self.state.write().await;
        state.strict_mode_active = false;
        state.strict_mode_reason = None;
        state.strict_mode_activated_at = None;
        
        info!("Strict mode manually deactivated");
        self.deactivate_strict_mode_metrics().await;
    }

    /// Get current queue length
    pub async fn queue_length(&self) -> usize {
        self.queue.read().await.len()
    }

    /// Check if strict mode is active
    pub async fn is_strict_mode_active(&self) -> bool {
        self.state.read().await.strict_mode_active
    }
}

/// Queue operation errors
#[derive(Debug, thiserror::Error)]
pub enum QueueError {
    #[error("Queue is full: current length {current_length}, max length {max_length}")]
    QueueFull { current_length: usize, max_length: usize },
    
    #[error("Item dropped: {reason} (detector: {detector_type})")]
    ItemDropped { reason: String, detector_type: String },
    
    #[error("Semaphore acquisition failed")]
    SemaphoreAcquisitionFailed,
    
    #[error("Dequeue timeout")]
    DequeueTimeout,
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_queue_manager_creation() {
        let config = QueueManagerConfig::default();
        let manager = QueueManager::new(config);
        
        assert_eq!(manager.queue_length().await, 0);
        assert!(!manager.is_strict_mode_active().await);
    }

    #[tokio::test]
    async fn test_enqueue_dequeue() {
        let config = QueueManagerConfig::default();
        let manager = QueueManager::new(config);
        
        let item = QueueItem {
            id: "test-1".to_string(),
            priority: Priority::Normal,
            detector_type: "pii_detector".to_string(),
            created_at: Instant::now(),
            tenant: "test-tenant".to_string(),
            payload_size: 1024,
        };
        
        // Enqueue item
        assert!(manager.enqueue(item.clone()).await.is_ok());
        assert_eq!(manager.queue_length().await, 1);
        
        // Dequeue item
        let dequeued = manager.dequeue(Duration::from_millis(100)).await.unwrap();
        assert!(dequeued.is_some());
        assert_eq!(dequeued.unwrap().id, "test-1");
        assert_eq!(manager.queue_length().await, 0);
    }

    #[tokio::test]
    async fn test_strict_mode_activation() {
        let mut config = QueueManagerConfig::default();
        config.max_queue_length = 10;
        config.strict_mode_threshold = 0.5; // 50%
        
        let manager = QueueManager::new(config);
        
        // Fill queue to trigger strict mode
        for i in 0..6 {
            let item = QueueItem {
                id: format!("test-{}", i),
                priority: Priority::Normal,
                detector_type: "pii_detector".to_string(),
                created_at: Instant::now(),
                tenant: "test-tenant".to_string(),
                payload_size: 1024,
            };
            manager.enqueue(item).await.unwrap();
        }
        
        // Wait for strict mode activation
        sleep(Duration::from_millis(100)).await;
        
        assert!(manager.is_strict_mode_active().await);
        
        let state = manager.get_state().await;
        assert!(state.strict_mode_reason.is_some());
    }

    #[tokio::test]
    async fn test_non_critical_dropping() {
        let mut config = QueueManagerConfig::default();
        config.max_queue_length = 10;
        config.strict_mode_threshold = 0.5;
        
        let manager = QueueManager::new(config);
        
        // Fill queue to trigger strict mode
        for i in 0..6 {
            let item = QueueItem {
                id: format!("test-{}", i),
                priority: Priority::Normal,
                detector_type: "pii_detector".to_string(),
                created_at: Instant::now(),
                tenant: "test-tenant".to_string(),
                payload_size: 1024,
            };
            manager.enqueue(item).await.unwrap();
        }
        
        // Wait for strict mode activation
        sleep(Duration::from_millis(100)).await;
        
        // Try to enqueue non-critical item
        let non_critical_item = QueueItem {
            id: "non-critical".to_string(),
            priority: Priority::Normal,
            detector_type: "nlp_detector".to_string(),
            created_at: Instant::now(),
            tenant: "test-tenant".to_string(),
            payload_size: 1024,
        };
        
        let result = manager.enqueue(non_critical_item).await;
        assert!(result.is_err());
        
        if let Err(QueueError::ItemDropped { reason, detector_type }) = result {
            assert_eq!(reason, "strict_mode_active");
            assert_eq!(detector_type, "nlp_detector");
        } else {
            panic!("Expected ItemDropped error");
        }
    }
}
