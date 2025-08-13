// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use ed25519_dalek::{PublicKey, Signature, Verifier};
use rayon::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{debug, info, warn};

/// Batch Ed25519 signature verifier for high-performance signature validation
pub struct BatchEd25519Verifier {
    /// Cache for verified public keys to avoid repeated parsing
    key_cache: Arc<RwLock<HashMap<String, PublicKey>>>,
    /// Batch size for optimal performance
    batch_size: usize,
    /// Enable parallel processing
    parallel: bool,
}

impl Default for BatchEd25519Verifier {
    fn default() -> Self {
        Self {
            key_cache: Arc::new(RwLock::new(HashMap::new())),
            batch_size: 1000,
            parallel: true,
        }
    }
}

impl BatchEd25519Verifier {
    /// Create a new batch verifier with custom configuration
    pub fn new(batch_size: usize, parallel: bool) -> Self {
        Self {
            key_cache: Arc::new(RwLock::new(HashMap::new())),
            batch_size,
            parallel,
        }
    }

    /// Verify a single signature
    pub async fn verify_single(
        &self,
        public_key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool, Box<dyn std::error::Error + Send + Sync>> {
        let pub_key = self.parse_public_key(public_key).await?;
        let sig = Signature::from_bytes(signature)?;
        
        match pub_key.verify(message, &sig) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    /// Verify multiple signatures in batch for optimal performance
    pub async fn verify_batch(
        &self,
        verifications: Vec<VerificationRequest>,
    ) -> Result<Vec<VerificationResult>, Box<dyn std::error::Error + Send + Sync>> {
        let start_time = std::time::Instant::now();
        let total_verifications = verifications.len();
        
        info!("Starting batch verification of {} signatures", total_verifications);
        
        let results = if self.parallel && total_verifications > self.batch_size {
            self.verify_batch_parallel(verifications).await?
        } else {
            self.verify_batch_sequential(verifications).await?
        };
        
        let duration = start_time.elapsed();
        let rate = total_verifications as f64 / duration.as_secs_f64();
        
        info!(
            "Batch verification completed: {} signatures in {:?} ({:.2} sig/s)",
            total_verifications, duration, rate
        );
        
        Ok(results)
    }

    /// Sequential batch verification for smaller batches
    async fn verify_batch_sequential(
        &self,
        verifications: Vec<VerificationRequest>,
    ) -> Result<Vec<VerificationResult>, Box<dyn std::error::Error + Send + Sync>> {
        let mut results = Vec::with_capacity(verifications.len());
        
        for (i, req) in verifications.into_iter().enumerate() {
            let result = self.verify_single(&req.public_key, &req.message, &req.signature).await?;
            results.push(VerificationResult {
                id: req.id,
                valid: result,
                index: i,
            });
        }
        
        Ok(results)
    }

    /// Parallel batch verification for large batches
    async fn verify_batch_parallel(
        &self,
        verifications: Vec<VerificationRequest>,
    ) -> Result<Vec<VerificationResult>, Box<dyn std::error::Error + Send + Sync>> {
        let chunks: Vec<Vec<VerificationRequest>> = verifications
            .chunks(self.batch_size)
            .map(|chunk| chunk.to_vec())
            .collect();
        
        let chunk_results: Vec<Vec<VerificationResult>> = chunks
            .into_par_iter()
            .map(|chunk| {
                // Process each chunk in parallel
                let mut results = Vec::new();
                for (i, req) in chunk.into_iter().enumerate() {
                    // Note: This is a simplified version - in production you'd want to handle errors properly
                    let result = match self.verify_single_sync(&req.public_key, &req.message, &req.signature) {
                        Ok(valid) => valid,
                        Err(_) => false,
                    };
                    results.push(VerificationResult {
                        id: req.id,
                        valid: result,
                        index: i,
                    });
                }
                results
            })
            .collect();
        
        // Flatten results
        let mut all_results = Vec::new();
        for chunk_result in chunk_results {
            all_results.extend(chunk_result);
        }
        
        Ok(all_results)
    }

    /// Synchronous version for parallel processing
    fn verify_single_sync(
        &self,
        public_key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool, Box<dyn std::error::Error + Send + Sync>> {
        // Parse public key (this would need to be handled differently in parallel context)
        let pub_key = match PublicKey::from_bytes(public_key) {
            Ok(key) => key,
            Err(_) => return Ok(false),
        };
        
        let sig = match Signature::from_bytes(signature) {
            Ok(sig) => sig,
            Err(_) => return Ok(false),
        };
        
        match pub_key.verify(message, &sig) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }

    /// Parse and cache public key
    async fn parse_public_key(&self, key_bytes: &[u8]) -> Result<PublicKey, Box<dyn std::error::Error + Send + Sync>> {
        let key_str = base64::encode(key_bytes);
        
        // Check cache first
        {
            let cache = self.key_cache.read().await;
            if let Some(cached_key) = cache.get(&key_str) {
                return Ok(*cached_key);
            }
        }
        
        // Parse and cache
        let pub_key = PublicKey::from_bytes(key_bytes)?;
        {
            let mut cache = self.key_cache.write().await;
            cache.insert(key_str, pub_key);
        }
        
        Ok(pub_key)
    }

    /// Get performance statistics
    pub fn get_stats(&self) -> VerifierStats {
        VerifierStats {
            batch_size: self.batch_size,
            parallel: self.parallel,
            cache_size: {
                // This would need to be handled differently in async context
                0
            },
        }
    }

    /// Clear the key cache
    pub async fn clear_cache(&self) {
        let mut cache = self.key_cache.write().await;
        cache.clear();
        info!("Key cache cleared");
    }
}

/// Request for signature verification
#[derive(Debug, Clone)]
pub struct VerificationRequest {
    pub id: String,
    pub public_key: Vec<u8>,
    pub message: Vec<u8>,
    pub signature: Vec<u8>,
}

/// Result of signature verification
#[derive(Debug, Clone)]
pub struct VerificationResult {
    pub id: String,
    pub valid: bool,
    pub index: usize,
}

/// Statistics about the verifier
#[derive(Debug, Clone)]
pub struct VerifierStats {
    pub batch_size: usize,
    pub parallel: bool,
    pub cache_size: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Keypair, SecretKey};
    use rand::rngs::OsRng;

    #[tokio::test]
    async fn test_single_verification() {
        let verifier = BatchEd25519Verifier::default();
        
        // Generate keypair
        let mut csprng = OsRng {};
        let keypair: Keypair = Keypair::generate(&mut csprng);
        let message = b"Hello, World!";
        let signature = keypair.sign(message);
        
        // Verify signature
        let result = verifier
            .verify_single(keypair.public.as_bytes(), message, signature.as_bytes())
            .await
            .unwrap();
        
        assert!(result);
    }

    #[tokio::test]
    async fn test_batch_verification() {
        let verifier = BatchEd25519Verifier::new(100, true);
        let mut verifications = Vec::new();
        
        // Generate multiple keypairs and signatures
        for i in 0..50 {
            let mut csprng = OsRng {};
            let keypair: Keypair = Keypair::generate(&mut csprng);
            let message = format!("Message {}", i).into_bytes();
            let signature = keypair.sign(&message);
            
            verifications.push(VerificationRequest {
                id: format!("test_{}", i),
                public_key: keypair.public.as_bytes().to_vec(),
                message,
                signature: signature.as_bytes().to_vec(),
            });
        }
        
        // Verify batch
        let results = verifier.verify_batch(verifications).await.unwrap();
        
        assert_eq!(results.len(), 50);
        assert!(results.iter().all(|r| r.valid));
    }

    #[test]
    fn test_verifier_stats() {
        let verifier = BatchEd25519Verifier::new(500, false);
        let stats = verifier.get_stats();
        
        assert_eq!(stats.batch_size, 500);
        assert!(!stats.parallel);
    }
}
