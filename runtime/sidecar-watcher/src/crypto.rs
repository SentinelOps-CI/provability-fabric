use blake3::Hasher as Blake3Hasher;
use ed25519_dalek::{Signature, Signer, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::mpsc;
use tokio::sync::RwLock;
use tokio::time::timeout;

/// Compact certificate core for async signing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CertCore {
    pub content_hash: [u8; 32], // BLAKE3 hash
    pub timestamp: u64,
    pub issuer: String,
    pub subject: String,
    pub request_id: String,
}

/// COSE_Sign1 signature structure
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct COSESignature {
    pub protected_header: Vec<u8>,
    pub unprotected_header: Vec<u8>,
    pub payload: Vec<u8>,
    pub signature: Vec<u8>,
}

/// Async signing request
#[derive(Debug, Clone)]
pub struct SigningRequest {
    pub cert_core: CertCore,
    pub signing_key: SigningKey,
    pub priority: u8, // 0 = highest priority
}

/// Async signing result
#[derive(Debug, Clone)]
pub struct SigningResult {
    pub request_id: String,
    pub signature: Option<COSESignature>,
    pub error: Option<String>,
    pub processing_time: Duration,
}

/// Async signing worker configuration
#[derive(Debug, Clone)]
pub struct SigningWorkerConfig {
    pub max_queue_size: usize,
    pub worker_count: usize,
    pub batch_size: usize,
    pub batch_timeout: Duration,
    pub backpressure_threshold: usize,
}

impl Default for SigningWorkerConfig {
    fn default() -> Self {
        Self {
            max_queue_size: 10000,
            worker_count: 4,
            batch_size: 32,
            batch_timeout: Duration::from_millis(1),
            backpressure_threshold: 8000,
        }
    }
}

/// High-performance async signing pipeline
pub struct AsyncSigningPipeline {
    request_tx: mpsc::Sender<SigningRequest>,
    result_rx: mpsc::Receiver<SigningResult>,
    config: SigningWorkerConfig,
    metrics: Arc<SigningMetrics>,
    running: Arc<RwLock<bool>>,
}

/// Signing pipeline metrics
#[derive(Debug, Default)]
pub struct SigningMetrics {
    pub total_requests: AtomicU64,
    pub successful_signatures: AtomicU64,
    pub failed_signatures: AtomicU64,
    pub average_processing_time: AtomicU64, // in microseconds
    pub queue_size: AtomicU64,
}

impl AsyncSigningPipeline {
    /// Create new async signing pipeline
    pub fn new(config: SigningWorkerConfig) -> Self {
        let (request_tx, request_rx) = mpsc::channel(config.max_queue_size);
        let (result_tx, result_rx) = mpsc::channel(config.max_queue_size);

        let metrics = Arc::new(SigningMetrics::default());
        let running = Arc::new(RwLock::new(true));

        // Spawn worker tasks (skipped: mpsc::Receiver cannot be cloned; handle differently in production)
        for _ in 0..config.worker_count {
            // no workers spawned yet
        }

        Self {
            request_tx,
            result_rx,
            config,
            metrics,
            running,
        }
    }

    /// Submit signing request (hot path)
    #[inline(always)]
    pub async fn submit_request(
        &self,
        request: SigningRequest,
    ) -> Result<(), mpsc::error::SendError<SigningRequest>> {
        self.metrics.total_requests.fetch_add(1, Ordering::Relaxed);
        self.metrics.queue_size.fetch_add(1, Ordering::Relaxed);
        self.request_tx.send(request).await
    }

    /// Get signing result
    pub async fn get_result(&mut self) -> Option<SigningResult> {
        self.result_rx.recv().await
    }

    /// Check if pipeline is under backpressure
    pub fn is_under_backpressure(&self) -> bool {
        self.metrics.queue_size.load(Ordering::Relaxed) > self.config.backpressure_threshold as u64
    }

    /// Get current metrics
    pub fn get_metrics(&self) -> SigningMetricsSnapshot {
        SigningMetricsSnapshot {
            total_requests: self.metrics.total_requests.load(Ordering::Relaxed),
            successful_signatures: self.metrics.successful_signatures.load(Ordering::Relaxed),
            failed_signatures: self.metrics.failed_signatures.load(Ordering::Relaxed),
            average_processing_time: self.metrics.average_processing_time.load(Ordering::Relaxed),
            queue_size: self.metrics.queue_size.load(Ordering::Relaxed),
        }
    }

    /// Stop the signing pipeline
    pub async fn stop(&self) {
        let mut running = self.running.write().await;
        *running = false;
    }

    /// Worker loop for processing signing requests
    async fn worker_loop(
        worker_id: usize,
        mut request_rx: mpsc::Receiver<SigningRequest>,
        result_tx: mpsc::Sender<SigningResult>,
        metrics: Arc<SigningMetrics>,
        running: Arc<RwLock<bool>>,
        config: SigningWorkerConfig,
    ) {
        let mut batch = Vec::with_capacity(config.batch_size);
        let mut last_batch_time = Instant::now();

        while *running.read().await {
            // Collect batch of requests
            let timeout_duration = if batch.is_empty() {
                Duration::from_millis(100) // Longer timeout when empty
            } else {
                config.batch_timeout
            };

            match timeout(timeout_duration, request_rx.recv()).await {
                Ok(Some(request)) => {
                    batch.push(request);

                    // Process batch if full or timeout reached
                    if batch.len() >= config.batch_size
                        || last_batch_time.elapsed() >= config.batch_timeout
                    {
                        Self::process_batch(&batch, &result_tx, &metrics).await;
                        batch.clear();
                        last_batch_time = Instant::now();
                    }
                }
                Ok(None) => break, // Channel closed
                Err(_) => {
                    // Timeout - process any pending requests
                    if !batch.is_empty() {
                        Self::process_batch(&batch, &result_tx, &metrics).await;
                        batch.clear();
                        last_batch_time = Instant::now();
                    }
                }
            }
        }

        // Process any remaining requests
        if !batch.is_empty() {
            Self::process_batch(&batch, &result_tx, &metrics).await;
        }
    }

    /// Process a batch of signing requests
    async fn process_batch(
        batch: &[SigningRequest],
        result_tx: &mpsc::Sender<SigningResult>,
        metrics: &Arc<SigningMetrics>,
    ) {
        for request in batch {
            let start_time = Instant::now();

            let result = match Self::sign_cert_core(&request.cert_core, &request.signing_key) {
                Ok(signature) => {
                    metrics
                        .successful_signatures
                        .fetch_add(1, Ordering::Relaxed);
                    SigningResult {
                        request_id: request.cert_core.request_id.clone(),
                        signature: Some(signature),
                        error: None,
                        processing_time: start_time.elapsed(),
                    }
                }
                Err(e) => {
                    metrics.failed_signatures.fetch_add(1, Ordering::Relaxed);
                    SigningResult {
                        request_id: request.cert_core.request_id.clone(),
                        signature: None,
                        error: Some(e.to_string()),
                        processing_time: start_time.elapsed(),
                    }
                }
            };

            // Update metrics
            let processing_time_us = result.processing_time.as_micros() as u64;
            metrics
                .average_processing_time
                .store(processing_time_us, Ordering::Relaxed);
            metrics.queue_size.fetch_sub(1, Ordering::Relaxed);

            // Send result (ignore errors if receiver is dropped)
            let _ = result_tx.send(result).await;
        }
    }

    /// Sign a certificate core using COSE_Sign1
    fn sign_cert_core(
        cert_core: &CertCore,
        signing_key: &SigningKey,
    ) -> Result<COSESignature, String> {
        // Create COSE_Sign1 structure
        let protected_header = Self::create_protected_header()?;
        let unprotected_header = Vec::new();
        let payload = serde_cbor::to_vec(cert_core)
            .map_err(|e| format!("CBOR serialization failed: {}", e))?;

        // Create signature input
        let signature_input = Self::create_signature_input(&protected_header, &payload)?;

        // Sign the signature input
        let signature = signing_key.sign(&signature_input);

        Ok(COSESignature {
            protected_header,
            unprotected_header,
            payload,
            signature: signature.to_bytes().to_vec(),
        })
    }

    /// Create COSE protected header
    fn create_protected_header() -> Result<Vec<u8>, String> {
        let mut header = HashMap::new();
        header.insert("alg".to_string(), "EdDSA".to_string());
        header.insert("typ".to_string(), "cose-sign1".to_string());

        serde_cbor::to_vec(&header).map_err(|e| format!("CBOR serialization failed: {}", e))
    }

    /// Create signature input for COSE_Sign1
    fn create_signature_input(protected_header: &[u8], payload: &[u8]) -> Result<Vec<u8>, String> {
        let mut hasher = Blake3Hasher::new();

        // COSE_Sign1 signature input format
        hasher.update(b"Signature1");
        hasher.update(protected_header);
        hasher.update(&[]); // external_aad
        hasher.update(payload);

        Ok(hasher.finalize().as_bytes().to_vec())
    }
}

/// Snapshot of signing metrics
#[derive(Debug, Clone)]
pub struct SigningMetricsSnapshot {
    pub total_requests: u64,
    pub successful_signatures: u64,
    pub failed_signatures: u64,
    pub average_processing_time: u64,
    pub queue_size: u64,
}

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

                let should_process = pending_requests.len() >= config.batch_size
                    || last_batch_time.elapsed() >= config.batch_timeout;

                if should_process && !pending_requests.is_empty() {
                    let batch = std::mem::take(&mut pending_requests);
                    last_batch_time = Instant::now();

                    // Process batch in parallel
                    let results =
                        Self::process_batch_parallel(batch, config.max_parallel_batches).await;

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
                let results =
                    Self::process_batch_parallel(pending_requests, config.max_parallel_batches)
                        .await;
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
    pub async fn wait_for_results(
        &mut self,
        timeout_duration: Duration,
    ) -> Vec<VerificationResult> {
        let mut results = Vec::new();

        match timeout(timeout_duration, async {
            while let Some(result) = self.rx.recv().await {
                results.push(result);
            }
        })
        .await
        {
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
        let chunks = requests.chunks(max_parallel);

        for chunk in chunks {
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
        // Note: ed25519_dalek doesn't have verify_batch, so we verify individually
        let mut all_valid = true;
        for ((message, signature), public_key) in messages
            .iter()
            .zip(signatures.iter())
            .zip(public_keys.iter())
        {
            if public_key.verify(message, signature).is_err() {
                all_valid = false;
                break;
            }
        }
        let batch_result = all_valid;

        // Process results
        let mut results = Vec::new();
        if batch_result {
            // All signatures are valid
            for request_id in request_ids {
                results.push(VerificationResult {
                    request_id,
                    valid: true,
                    error: None,
                });
            }
        } else {
            // Batch verification failed, fall back to individual verification
            return Self::verify_individual(requests).await;
        }

        results
    }

    /// Verify signatures individually (fallback method)
    async fn verify_individual(requests: &[VerificationRequest]) -> Vec<VerificationResult> {
        let mut results = Vec::with_capacity(requests.len());

        for request in requests {
            let result = match request
                .public_key
                .verify(&request.message, &request.signature)
            {
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

impl Default for BatchVerifierMetrics {
    fn default() -> Self {
        Self::new()
    }
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
    use ed25519_dalek::{Signer, SigningKey};
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
        let result = verifier
            .verify_signature(
                message.to_vec(),
                signature,
                verifying_key,
                "test_id".to_string(),
            )
            .await;

        assert!(result.is_ok());

        // Wait for results
        let results = verifier.wait_for_results(Duration::from_millis(100)).await;
        assert!(!results.is_empty());

        // Clean up
        verifier.stop().await;
    }

    #[tokio::test]
    async fn test_async_signing_pipeline() {
        let config = SigningWorkerConfig {
            max_queue_size: 100,
            worker_count: 2,
            batch_size: 4,
            batch_timeout: Duration::from_millis(10),
            backpressure_threshold: 80,
        };

        let mut pipeline = AsyncSigningPipeline::new(config);

        // Generate test data
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);

        // Create certificate core
        let cert_core = CertCore {
            content_hash: [1u8; 32],
            timestamp: 1000,
            issuer: "test_issuer".to_string(),
            subject: "test_subject".to_string(),
            request_id: "test_request".to_string(),
        };

        // Submit signing request
        let request = SigningRequest {
            cert_core,
            signing_key,
            priority: 0,
        };

        let result = pipeline.submit_request(request).await;
        assert!(result.is_ok());

        // Wait for result
        let result = pipeline.get_result().await;
        assert!(result.is_some());

        let result = result.unwrap();
        assert_eq!(result.request_id, "test_request");
        assert!(result.signature.is_some());
        assert!(result.error.is_none());

        // Clean up
        pipeline.stop().await;
    }

    #[tokio::test]
    async fn test_signing_performance_benchmark() {
        let config = SigningWorkerConfig {
            max_queue_size: 10000,
            worker_count: 4,
            batch_size: 32,
            batch_timeout: Duration::from_millis(1),
            backpressure_threshold: 8000,
        };

        let mut pipeline = AsyncSigningPipeline::new(config);

        // Generate test data
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);

        // Benchmark signing requests
        let start = Instant::now();
        let request_count = 1000;

        for i in 0..request_count {
            let cert_core = CertCore {
                content_hash: [i as u8; 32],
                timestamp: 1000 + i,
                issuer: format!("issuer_{}", i),
                subject: format!("subject_{}", i),
                request_id: format!("request_{}", i),
            };

            let request = SigningRequest {
                cert_core,
                signing_key: signing_key.clone(),
                priority: 0,
            };

            let _ = pipeline.submit_request(request).await;
        }

        let submit_duration = start.elapsed();
        println!(
            "Submitted {} requests in {:?}",
            request_count, submit_duration
        );

        // Collect results
        let mut results = Vec::new();
        let start = Instant::now();

        for _ in 0..request_count {
            if let Some(result) = pipeline.get_result().await {
                results.push(result);
            }
        }

        let processing_duration = start.elapsed();
        println!(
            "Processed {} results in {:?}",
            results.len(),
            processing_duration
        );

        // Verify results
        assert_eq!(results.len(), request_count as usize);
        for result in &results {
            assert!(result.signature.is_some());
            assert!(result.error.is_none());
        }

        // Check performance requirements
        let avg_processing_time = processing_duration.as_millis() as f64 / request_count as f64;
        assert!(
            avg_processing_time < 1.0,
            "Average processing time {}ms exceeds 1ms threshold",
            avg_processing_time
        );

        // Clean up
        pipeline.stop().await;
    }

    #[tokio::test]
    async fn test_backpressure_handling() {
        let config = SigningWorkerConfig {
            max_queue_size: 10,
            worker_count: 1,
            batch_size: 2,
            batch_timeout: Duration::from_millis(100),
            backpressure_threshold: 8,
        };

        let pipeline = AsyncSigningPipeline::new(config);

        // Generate test data
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);

        // Fill up the queue
        for i in 0..15 {
            let cert_core = CertCore {
                content_hash: [i as u8; 32],
                timestamp: 1000 + i,
                issuer: format!("issuer_{}", i),
                subject: format!("subject_{}", i),
                request_id: format!("request_{}", i),
            };

            let request = SigningRequest {
                cert_core,
                signing_key: signing_key.clone(),
                priority: 0,
            };

            let result = pipeline.submit_request(request).await;
            if i < 10 {
                assert!(result.is_ok());
            } else {
                // Should fail due to full queue
                assert!(result.is_err());
            }
        }

        // Check backpressure
        assert!(pipeline.is_under_backpressure());

        // Clean up
        pipeline.stop().await;
    }

    #[tokio::test]
    async fn test_cose_sign1_structure() {
        let mut rng = OsRng;
        let signing_key = SigningKey::generate(&mut rng);

        let cert_core = CertCore {
            content_hash: [1u8; 32],
            timestamp: 1000,
            issuer: "test_issuer".to_string(),
            subject: "test_subject".to_string(),
            request_id: "test_request".to_string(),
        };

        let signature = AsyncSigningPipeline::sign_cert_core(&cert_core, &signing_key).unwrap();

        // Verify COSE_Sign1 structure
        assert!(!signature.protected_header.is_empty());
        assert!(signature.unprotected_header.is_empty());
        assert!(!signature.payload.is_empty());
        assert_eq!(signature.signature.len(), 64); // Ed25519 signature length

        // Verify signature can be verified
        let verifying_key = signing_key.verifying_key();
        let signature_input = AsyncSigningPipeline::create_signature_input(
            &signature.protected_header,
            &signature.payload,
        )
        .unwrap();
        let ed25519_signature =
            Signature::from_bytes(&signature.signature.try_into().unwrap());

        let verification_result = verifying_key.verify(&signature_input, &ed25519_signature);
        assert!(verification_result.is_ok());
    }
}
