use ed25519_dalek::{VerifyingKey, Signature, Verifier};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use tokio::time::{sleep, timeout};
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// Message to be verified with its signature and public key
#[derive(Debug, Clone)]
pub struct VerificationRequest {
    pub message: Vec<u8>,
    pub signature: Signature,
    pub public_key: VerifyingKey,
    pub request_id: String,
}

/// Result of a verification operation
#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub request_id: String,
    pub valid: bool,
    pub error: Option<String>,
}

/// Batch verification aggregator
pub struct BatchVerifier {
    tx: mpsc::Sender<VerificationRequest>,
    rx: mpsc::Receiver<VerificationResult>,
    batch_size: usize,
    batch_timeout: Duration,
    running: Arc<RwLock<bool>>,
}

/// Configuration for batch verification
#[derive(Debug, Clone)]
pub struct BatchVerifierConfig {
    pub batch_size: usize,
    pub batch_timeout: Duration,
    pub max_parallel_batches: usize,
}

impl Default for BatchVerifierConfig {
    fn default() -> Self {
        Self {
            batch_size: 64,
            batch_timeout: Duration::from_millis(2),
            max_parallel_batches: 4,
        }
    }
}

impl BatchVerifier {
    /// Create a new batch verifier
    pub fn new(config: BatchVerifierConfig) -> Self {
        let (tx, mut rx) = mpsc::channel::<VerificationRequest>(1000);
        let (result_tx, result_rx) = mpsc::channel::<VerificationResult>(1000);
        
        let running = Arc::new(RwLock::new(true));
        let running_clone = running.clone();
        
        // Spawn the batch processing worker
        tokio::spawn(async move {
            let mut pending_requests: Vec<VerificationRequest> = Vec::new();
            let mut last_batch_time = Instant::now();
            
            while let Some(request) = rx.recv().await {
                pending_requests.push(request);
                
                let should_process = pending_requests.len() >= config.batch_size ||
                    last_batch_time.elapsed() >= config.batch_timeout;
                
                if should_process && !pending_requests.is_empty() {
                    let batch = std::mem::take(&mut pending_requests);
                    last_batch_time = Instant::now();
                    
                    // Process batch in parallel
                    let results = Self::process_batch_parallel(batch, config.max_parallel_batches).await;
                    
                    // Send results back
                    for result in results {
                        if result_tx.send(result).await.is_err() {
                            break;
                        }
                    }
                }
            }
            
            // Process any remaining requests
            if !pending_requests.is_empty() {
                let results = Self::process_batch_parallel(pending_requests, config.max_parallel_batches).await;
                for result in results {
                    let _ = result_tx.send(result).await;
                }
            }
        });
        
        Self {
            tx,
            rx: result_rx,
            batch_size: config.batch_size,
            batch_timeout: config.batch_timeout,
            running,
        }
    }
    
    /// Submit a verification request for batch processing
    pub async fn verify_signature(
        &self,
        message: Vec<u8>,
        signature: Signature,
        public_key: VerifyingKey,
        request_id: String,
    ) -> Result<(), mpsc::error::SendError<VerificationRequest>> {
        let request = VerificationRequest {
            message,
            signature,
            public_key,
            request_id,
        };
        
        self.tx.send(request).await
    }
    
    /// Wait for verification results
    pub async fn wait_for_results(&mut self, timeout_duration: Duration) -> Vec<VerificationResult> {
        let mut results = Vec::new();
        
        match timeout(timeout_duration, async {
            while let Some(result) = self.rx.recv().await {
                results.push(result);
            }
        }).await {
            Ok(_) => results,
            Err(_) => results, // Return what we got before timeout
        }
    }
    
    /// Process a batch of verification requests in parallel
    async fn process_batch_parallel(
        requests: Vec<VerificationRequest>,
        max_parallel: usize,
    ) -> Vec<VerificationResult> {
        let mut results = Vec::with_capacity(requests.len());
        let mut chunks = requests.chunks(max_parallel);
        
        while let Some(chunk) = chunks.next() {
            let chunk_results = Self::process_batch_single(chunk).await;
            results.extend(chunk_results);
        }
        
        results
    }
    
    /// Process a single batch of verification requests
    async fn process_batch_single(requests: &[VerificationRequest]) -> Vec<VerificationResult> {
        if requests.len() < 4 {
            // Fallback to individual verification for small batches
            return Self::verify_individual(requests).await;
        }
        
        // Prepare batch verification data
        let mut messages = Vec::new();
        let mut signatures = Vec::new();
        let mut public_keys = Vec::new();
        let mut request_ids = Vec::new();
        
        for request in requests {
            messages.push(&request.message[..]);
            signatures.push(request.signature);
            public_keys.push(request.public_key);
            request_ids.push(request.request_id.clone());
        }
        
        // Perform batch verification
        let batch_result = ed25519_dalek::verify_batch(&messages, &signatures, &public_keys);
        
        // Process results
        let mut results = Vec::new();
        match batch_result {
            Ok(_) => {
                // All signatures are valid
                for request_id in request_ids {
                    results.push(VerificationResult {
                        request_id,
                        valid: true,
                        error: None,
                    });
                }
            }
            Err(_) => {
                // Batch verification failed, fall back to individual verification
                return Self::verify_individual(requests).await;
            }
        }
        
        results
    }
    
    /// Verify signatures individually (fallback method)
    async fn verify_individual(requests: &[VerificationRequest]) -> Vec<VerificationResult> {
        let mut results = Vec::with_capacity(requests.len());
        
        for request in requests {
            let result = match request.public_key.verify(&request.message, &request.signature) {
                Ok(_) => VerificationResult {
                    request_id: request.request_id.clone(),
                    valid: true,
                    error: None,
                },
                Err(e) => VerificationResult {
                    request_id: request.request_id.clone(),
                    valid: false,
                    error: Some(e.to_string()),
                },
            };
            results.push(result);
        }
        
        results
    }
    
    /// Stop the batch verifier
    pub async fn stop(&self) {
        let mut running = self.running.write().await;
        *running = false;
    }
    
    /// Check if the verifier is running
    pub async fn is_running(&self) -> bool {
        *self.running.read().await
    }
}

/// Metrics for batch verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchVerifierMetrics {
    pub total_requests: u64,
    pub batch_requests: u64,
    pub individual_requests: u64,
    pub batch_success_rate: f64,
    pub average_batch_size: f64,
    pub total_processing_time: Duration,
}

impl BatchVerifierMetrics {
    pub fn new() -> Self {
        Self {
            total_requests: 0,
            batch_requests: 0,
            individual_requests: 0,
            batch_success_rate: 0.0,
            total_processing_time: Duration::ZERO,
            average_batch_size: 0.0,
        }
    }
    
    pub fn update_success_rate(&mut self, successful_batches: u64, total_batches: u64) {
        if total_batches > 0 {
            self.batch_success_rate = successful_batches as f64 / total_batches as f64;
        }
    }
    
    pub fn update_average_batch_size(&mut self, total_batch_size: u64, total_batches: u64) {
        if total_batches > 0 {
            self.average_batch_size = total_batch_size as f64 / total_batches as f64;
        }
    }
}

/// Convenience function for single signature verification
pub async fn verify_single_signature(
    message: &[u8],
    signature: &Signature,
    public_key: &VerifyingKey,
) -> Result<(), ed25519_dalek::ed25519::Error> {
    public_key.verify(message, signature)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{SigningKey, Signer};
    use rand::rngs::OsRng;
    
    #[tokio::test]
    async fn test_batch_verifier_creation() {
        let config = BatchVerifierConfig::default();
        let verifier = BatchVerifier::new(config);
        assert!(verifier.is_running().await);
    }
    
    #[tokio::test]
    async fn test_single_signature_verification() {
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);
        let verifying_key = signing_key.verifying_key();
        
        let message = b"test message";
        let signature = signing_key.sign(message);
        
        let result = verify_single_signature(message, &signature, &verifying_key).await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_batch_verification_workflow() {
        let config = BatchVerifierConfig {
            batch_size: 4,
            batch_timeout: Duration::from_millis(10),
            max_parallel_batches: 2,
        };
        
        let mut verifier = BatchVerifier::new(config);
        
        // Generate test data
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);
        let verifying_key = signing_key.verifying_key();
        
        let message = b"test message";
        let signature = signing_key.sign(message);
        
        // Submit verification request
        let result = verifier.verify_signature(
            message.to_vec(),
            signature,
            verifying_key,
            "test_id".to_string(),
        ).await;
        
        assert!(result.is_ok());
        
        // Wait for results
        let results = verifier.wait_for_results(Duration::from_millis(100)).await;
        assert!(!results.is_empty());
        
        // Clean up
        verifier.stop().await;
    }
}
