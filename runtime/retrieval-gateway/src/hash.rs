use blake3::Hasher;
use sha2::{Sha256, Digest};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

/// Hash algorithm types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum HashAlgorithm {
    SHA256,
    BLAKE3,
}

impl std::fmt::Display for HashAlgorithm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HashAlgorithm::SHA256 => write!(f, "sha256"),
            HashAlgorithm::BLAKE3 => write!(f, "blake3"),
        }
    }
}

impl std::str::FromStr for HashAlgorithm {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "sha256" | "sha-256" => Ok(HashAlgorithm::SHA256),
            "blake3" | "blake-3" => Ok(HashAlgorithm::BLAKE3),
            _ => Err(format!("Unknown hash algorithm: {}", s)),
        }
    }
}

/// Hash result with metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HashResult {
    pub hash: String,
    pub algorithm: HashAlgorithm,
    pub created_at: u64,
    pub payload_size: usize,
}

/// Hash configuration
#[derive(Debug, Clone)]
pub struct HashConfig {
    pub default_algorithm: HashAlgorithm,
    pub blake3_threshold: usize, // Use BLAKE3 for payloads larger than this
    pub sha256_threshold: usize, // Use SHA-256 for payloads smaller than this
    pub transition_period_days: u64, // Days to accept old SHA-256 hashes
}

impl Default for HashConfig {
    fn default() -> Self {
        Self {
            default_algorithm: HashAlgorithm::BLAKE3,
            blake3_threshold: 1024, // 1KB
            sha256_threshold: 64,   // 64 bytes
            transition_period_days: 30,
        }
    }
}

/// Hash manager for handling different hashing algorithms
pub struct HashManager {
    config: HashConfig,
    hash_cache: Arc<RwLock<HashMap<String, HashResult>>>,
    metrics: Arc<RwLock<HashMetrics>>,
}

/// Hash performance metrics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HashMetrics {
    pub total_hashes: u64,
    pub sha256_hashes: u64,
    pub blake3_hashes: u64,
    pub cache_hits: u64,
    pub cache_misses: u64,
    pub average_hash_time_ns: u64,
}

impl Default for HashMetrics {
    fn default() -> Self {
        Self {
            total_hashes: 0,
            sha256_hashes: 0,
            blake3_hashes: 0,
            cache_hits: 0,
            cache_misses: 0,
            average_hash_time_ns: 0,
        }
    }
}

impl HashManager {
    /// Create a new hash manager
    pub fn new(config: HashConfig) -> Self {
        Self {
            config,
            hash_cache: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(HashMetrics::default())),
        }
    }

    /// Hash data with automatic algorithm selection
    pub async fn hash_data(&self, data: &[u8], force_algorithm: Option<HashAlgorithm>) -> HashResult {
        let start_time = std::time::Instant::now();
        
        // Determine which algorithm to use
        let algorithm = force_algorithm.unwrap_or_else(|| self.select_algorithm(data.len()));
        
        // Check cache first
        let cache_key = self.generate_cache_key(data, algorithm);
        if let Some(cached) = self.get_from_cache(&cache_key).await {
            self.update_metrics(true, algorithm, start_time.elapsed()).await;
            return cached;
        }
        
        // Perform hashing
        let hash = match algorithm {
            HashAlgorithm::SHA256 => self.hash_sha256(data),
            HashAlgorithm::BLAKE3 => self.hash_blake3(data),
        };
        
        let result = HashResult {
            hash,
            algorithm,
            created_at: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            payload_size: data.len(),
        };
        
        // Cache the result
        self.cache_result(&cache_key, &result).await;
        
        // Update metrics
        self.update_metrics(false, algorithm, start_time.elapsed()).await;
        
        result
    }

    /// Hash text content (commonly used for text_hash and result_hash)
    pub async fn hash_text(&self, text: &str) -> HashResult {
        let data = text.as_bytes();
        self.hash_data(data, Some(HashAlgorithm::BLAKE3)).await
    }

    /// Hash large payloads (certificates, receipts, etc.)
    pub async fn hash_large_payload(&self, data: &[u8]) -> HashResult {
        self.hash_data(data, Some(HashAlgorithm::BLAKE3)).await
    }

    /// Hash identifiers (small, fixed-size data)
    pub async fn hash_identifier(&self, data: &[u8]) -> HashResult {
        self.hash_data(data, Some(HashAlgorithm::SHA256)).await
    }

    /// Verify a hash against data
    pub async fn verify_hash(&self, data: &[u8], expected_hash: &str, algorithm: HashAlgorithm) -> bool {
        let result = self.hash_data(data, Some(algorithm)).await;
        result.hash == expected_hash
    }

    /// Verify hash with automatic algorithm detection
    pub async fn verify_hash_auto(&self, data: &[u8], expected_hash: &str) -> bool {
        // Try to detect algorithm from hash format
        let algorithm = self.detect_algorithm_from_hash(expected_hash);
        
        // If we can't detect, try both algorithms
        match algorithm {
            Some(alg) => self.verify_hash(data, expected_hash, alg).await,
            None => {
                // Try both algorithms
                self.verify_hash(data, expected_hash, HashAlgorithm::BLAKE3).await ||
                self.verify_hash(data, expected_hash, HashAlgorithm::SHA256).await
            }
        }
    }

    /// Get hash metrics
    pub async fn get_metrics(&self) -> HashMetrics {
        self.metrics.read().await.clone()
    }

    /// Clear hash cache
    pub async fn clear_cache(&self) {
        let mut cache = self.hash_cache.write().await;
        cache.clear();
    }

    /// Select the appropriate hashing algorithm based on data size
    fn select_algorithm(&self, data_size: usize) -> HashAlgorithm {
        if data_size >= self.config.blake3_threshold {
            HashAlgorithm::BLAKE3
        } else if data_size <= self.config.sha256_threshold {
            HashAlgorithm::SHA256
        } else {
            self.config.default_algorithm
        }
    }

    /// Generate SHA-256 hash
    fn hash_sha256(&self, data: &[u8]) -> String {
        let mut hasher = Sha256::new();
        hasher.update(data);
        hex::encode(hasher.finalize())
    }

    /// Generate BLAKE3 hash
    fn hash_blake3(&self, data: &[u8]) -> String {
        let mut hasher = Hasher::new();
        hasher.update(data);
        hex::encode(hasher.finalize())
    }

    /// Generate cache key for data and algorithm
    fn generate_cache_key(&self, data: &[u8], algorithm: HashAlgorithm) -> String {
        use sha2::Sha256;
        let mut hasher = Sha256::new();
        hasher.update(data);
        hasher.update(algorithm.to_string().as_bytes());
        hex::encode(hasher.finalize())
    }

    /// Get result from cache
    async fn get_from_cache(&self, key: &str) -> Option<HashResult> {
        let cache = self.hash_cache.read().await;
        cache.get(key).cloned()
    }

    /// Cache a hash result
    async fn cache_result(&self, key: &str, result: &HashResult) {
        let mut cache = self.hash_cache.write().await;
        cache.insert(key.to_string(), result.clone());
    }

    /// Update metrics
    async fn update_metrics(&self, cache_hit: bool, algorithm: HashAlgorithm, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        
        metrics.total_hashes += 1;
        if cache_hit {
            metrics.cache_hits += 1;
        } else {
            metrics.cache_misses += 1;
        }
        
        match algorithm {
            HashAlgorithm::SHA256 => metrics.sha256_hashes += 1,
            HashAlgorithm::BLAKE3 => metrics.blake3_hashes += 1,
        }
        
        // Update average hash time
        let duration_ns = duration.as_nanos() as u64;
        metrics.average_hash_time_ns = 
            (metrics.average_hash_time_ns * (metrics.total_hashes - 1) + duration_ns) / metrics.total_hashes;
    }

    /// Detect algorithm from hash format
    fn detect_algorithm_from_hash(&self, hash: &str) -> Option<HashAlgorithm> {
        // BLAKE3 hashes are typically 64 characters
        // SHA-256 hashes are typically 64 characters
        // This is a simple heuristic - in practice you might want to store algorithm metadata
        if hash.len() == 64 {
            // Could be either, but default to BLAKE3 for new hashes
            Some(HashAlgorithm::BLAKE3)
        } else {
            None
        }
    }
}

/// Convenience functions for common hashing operations
pub async fn hash_text_blake3(text: &str) -> String {
    let manager = HashManager::new(HashConfig::default());
    let result = manager.hash_text(text).await;
    result.hash
}

pub async fn hash_text_sha256(text: &str) -> String {
    let manager = HashManager::new(HashConfig::default());
    let result = manager.hash_identifier(text.as_bytes()).await;
    result.hash
}

/// Legacy function for backward compatibility
pub async fn hash_text_legacy(text: &str) -> String {
    hash_text_sha256(text).await
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_hash_manager_creation() {
        let config = HashConfig::default();
        let manager = HashManager::new(config);
        assert_eq!(manager.config.default_algorithm, HashAlgorithm::BLAKE3);
    }

    #[tokio::test]
    async fn test_algorithm_selection() {
        let config = HashConfig::default();
        let manager = HashManager::new(config);
        
        // Small data should use SHA-256
        let small_data = b"small";
        let result = manager.hash_data(small_data, None).await;
        assert_eq!(result.algorithm, HashAlgorithm::SHA256);
        
        // Large data should use BLAKE3
        let large_data = vec![0u8; 2048]; // 2KB
        let result = manager.hash_data(&large_data, None).await;
        assert_eq!(result.algorithm, HashAlgorithm::BLAKE3);
    }

    #[tokio::test]
    async fn test_hash_verification() {
        let config = HashConfig::default();
        let manager = HashManager::new(config);
        
        let data = b"test data";
        let result = manager.hash_data(data, None).await;
        
        let is_valid = manager.verify_hash(data, &result.hash, result.algorithm).await;
        assert!(is_valid);
    }

    #[tokio::test]
    async fn test_text_hashing() {
        let text = "This is a test text for hashing";
        let hash = hash_text_blake3(text).await;
        assert_eq!(hash.len(), 64);
        
        let sha256_hash = hash_text_sha256(text).await;
        assert_eq!(sha256_hash.len(), 64);
        
        // Hashes should be different
        assert_ne!(hash, sha256_hash);
    }

    #[tokio::test]
    async fn test_cache_functionality() {
        let config = HashConfig::default();
        let manager = HashManager::new(config);
        
        let data = b"test data for caching";
        
        // First hash should miss cache
        let result1 = manager.hash_data(data, None).await;
        
        // Second hash should hit cache
        let result2 = manager.hash_data(data, None).await;
        
        assert_eq!(result1.hash, result2.hash);
        
        let metrics = manager.get_metrics().await;
        assert_eq!(metrics.cache_hits, 1);
        assert_eq!(metrics.cache_misses, 1);
    }
}
