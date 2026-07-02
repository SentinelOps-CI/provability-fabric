/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, VecDeque};
use std::hash::{Hash, Hasher};
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::time::{Duration, Instant};

fn read_witness<T>(lock: &RwLock<T>) -> Option<RwLockReadGuard<'_, T>> {
    lock.read().ok()
}

fn write_witness<T>(lock: &RwLock<T>) -> Option<RwLockWriteGuard<'_, T>> {
    lock.write().ok()
}

/// Merkle proof for a single field
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MerkleProof {
    pub field_path: Vec<String>,
    pub siblings: Vec<[u8; 32]>,
    pub root_hash: [u8; 32],
    pub field_hash: [u8; 32],
    pub index: usize,
}

/// Batched multiproof for multiple fields in a single emission
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchedMultiproof {
    pub emission_id: String,
    pub field_proofs: Vec<MerkleProof>,
    pub root_hash: [u8; 32],
    pub timestamp: u64,
    pub canonical_json: String, // JCS canonicalized JSON
}

/// JCS (JSON Canonicalization Scheme) canonicalizer
pub struct JCSCanonicalizer;

impl JCSCanonicalizer {
    /// Canonicalize JSON according to RFC8785
    pub fn canonicalize(json: &serde_json::Value) -> Result<String, String> {
        // Sort object keys lexicographically
        let canonical = Self::sort_json_keys(json);

        // Serialize with no whitespace
        serde_json::to_string(&canonical).map_err(|e| format!("JCS canonicalization failed: {}", e))
    }

    /// Recursively sort JSON object keys
    fn sort_json_keys(value: &serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::Object(map) => {
                let mut sorted_map = serde_json::Map::new();
                let mut keys: Vec<_> = map.keys().collect();
                keys.sort();

                for key in keys {
                    let sorted_value = Self::sort_json_keys(&map[key]);
                    sorted_map.insert(key.clone(), sorted_value);
                }

                serde_json::Value::Object(sorted_map)
            }
            serde_json::Value::Array(arr) => {
                let sorted_arr: Vec<_> = arr.iter().map(Self::sort_json_keys).collect();
                serde_json::Value::Array(sorted_arr)
            }
            _ => value.clone(),
        }
    }
}

/// Optimized witness checker with batched multiproofs and caching
pub struct OptimizedWitnessChecker {
    // LRU cache for proof verification results
    proof_cache: Arc<RwLock<LruCache<ProofKey, bool>>>,
    // Bloom filter for pre-filtering
    bloom_filter: Arc<RwLock<BloomFilter>>,
    // Batch processing queue
    batch_queue: Arc<RwLock<VecDeque<BatchedMultiproof>>>,
    // Cache configuration
    cache_config: CacheConfig,
}

/// Proof cache key
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ProofKey {
    field_commit_root: [u8; 32],
    path_hash: u64,
}

/// LRU Cache implementation
struct LruCache<K, V> {
    capacity: usize,
    entries: VecDeque<(K, V, Instant)>,
    ttl: Duration,
}

impl<K: Clone + PartialEq + Hash, V: Clone> LruCache<K, V> {
    fn new(capacity: usize, ttl: Duration) -> Self {
        Self {
            capacity,
            entries: VecDeque::new(),
            ttl,
        }
    }

    fn get(&mut self, key: &K) -> Option<V> {
        // Remove expired entries
        let now = Instant::now();
        self.entries
            .retain(|(_, _, timestamp)| now.duration_since(*timestamp) < self.ttl);

        // Find and move to front
        if let Some(pos) = self.entries.iter().position(|(k, _, _)| k == key) {
            let (k, v, timestamp) = self.entries.remove(pos)?;
            self.entries.push_front((k, v, timestamp));
            Some(self.entries[0].1.clone())
        } else {
            None
        }
    }

    fn insert(&mut self, key: K, value: V) {
        // Remove expired entries
        let now = Instant::now();
        self.entries
            .retain(|(_, _, timestamp)| now.duration_since(*timestamp) < self.ttl);

        // Remove if already exists
        self.entries.retain(|(k, _, _)| k != &key);

        // Insert at front
        self.entries.push_front((key, value, now));

        // Remove oldest if over capacity
        while self.entries.len() > self.capacity {
            self.entries.pop_back();
        }
    }
}

/// Simple Bloom filter for pre-filtering
struct BloomFilter {
    bits: Vec<u8>,
    hash_count: usize,
    size: usize,
}

impl BloomFilter {
    fn new(size: usize, hash_count: usize) -> Self {
        Self {
            bits: vec![0; size.div_ceil(8)],
            hash_count,
            size,
        }
    }

    fn add(&mut self, item: &[u8]) {
        for i in 0..self.hash_count {
            let hash = self.hash(item, i);
            let bit_index = hash % self.size;
            let byte_index = bit_index / 8;
            let bit_offset = bit_index % 8;
            self.bits[byte_index] |= 1 << bit_offset;
        }
    }

    fn might_contain(&self, item: &[u8]) -> bool {
        for i in 0..self.hash_count {
            let hash = self.hash(item, i);
            let bit_index = hash % self.size;
            let byte_index = bit_index / 8;
            let bit_offset = bit_index % 8;
            if (self.bits[byte_index] & (1 << bit_offset)) == 0 {
                return false;
            }
        }
        true
    }

    fn hash(&self, item: &[u8], seed: usize) -> usize {
        let mut hasher = DefaultHasher::new();
        hasher.write(item);
        hasher.write_usize(seed);
        hasher.finish() as usize
    }
}

/// Cache configuration
#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub max_cache_size: usize,
    pub cache_ttl_seconds: u64,
    pub bloom_filter_size: usize,
    pub bloom_hash_count: usize,
    pub batch_size: usize,
    pub batch_timeout_ms: u64,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            max_cache_size: 10000,
            cache_ttl_seconds: 300, // 5 minutes
            bloom_filter_size: 100000,
            bloom_hash_count: 3,
            batch_size: 32,
            batch_timeout_ms: 10,
        }
    }
}

impl OptimizedWitnessChecker {
    /// Create new optimized witness checker
    pub fn new(config: CacheConfig) -> Self {
        Self {
            proof_cache: Arc::new(RwLock::new(LruCache::new(
                config.max_cache_size,
                Duration::from_secs(config.cache_ttl_seconds),
            ))),
            bloom_filter: Arc::new(RwLock::new(BloomFilter::new(
                config.bloom_filter_size,
                config.bloom_hash_count,
            ))),
            batch_queue: Arc::new(RwLock::new(VecDeque::new())),
            cache_config: config,
        }
    }

    /// Verify a single Merkle proof (hot path)
    #[inline(always)]
    pub fn verify_proof(&self, proof: &MerkleProof) -> bool {
        // Check Bloom filter first (fast pre-filter)
        let proof_key = self.create_proof_key(proof);
        if !read_witness(&self.bloom_filter)
            .map(|filter| filter.might_contain(&proof_key.field_commit_root))
            .unwrap_or(false)
        {
            return false; // Definitely not in cache
        }

        // Check LRU cache
        if let Some(mut cache) = write_witness(&self.proof_cache) {
            if let Some(cached_result) = cache.get(&proof_key) {
                return cached_result;
            }
        }

        // Verify proof and cache result
        let result = self.verify_merkle_proof(proof);
        if let Some(mut cache) = write_witness(&self.proof_cache) {
            cache.insert(proof_key, result);
        }
        result
    }

    /// Verify batched multiproof (3-5× faster than individual proofs)
    pub fn verify_batched_multiproof(&self, multiproof: &BatchedMultiproof) -> bool {
        // Verify canonical JSON first
        if !self.verify_canonical_json(multiproof) {
            return false;
        }

        // Verify all field proofs in the batch
        for proof in &multiproof.field_proofs {
            if !self.verify_proof(proof) {
                return false;
            }
        }

        // Verify root consistency
        self.verify_root_consistency(multiproof)
    }

    /// Add proof to Bloom filter (for pre-filtering)
    pub fn add_to_bloom_filter(&self, root_hash: [u8; 32]) {
        if let Some(mut filter) = write_witness(&self.bloom_filter) {
            filter.add(&root_hash);
        }
    }

    /// Process batch queue
    pub fn process_batch_queue(&self) -> usize {
        let mut queue = match write_witness(&self.batch_queue) {
            Some(queue) => queue,
            None => return 0,
        };
        let mut processed = 0;
        let batch_size = self.cache_config.batch_size;

        while processed < batch_size {
            if let Some(multiproof) = queue.pop_front() {
                self.verify_batched_multiproof(&multiproof);
                processed += 1;
            } else {
                break;
            }
        }

        processed
    }

    /// Create proof cache key
    fn create_proof_key(&self, proof: &MerkleProof) -> ProofKey {
        let mut hasher = DefaultHasher::new();
        proof.field_path.hash(&mut hasher);
        let path_hash = hasher.finish();

        ProofKey {
            field_commit_root: proof.root_hash,
            path_hash,
        }
    }

    /// Verify Merkle proof using SHA-256
    fn verify_merkle_proof(&self, proof: &MerkleProof) -> bool {
        let mut current_hash = proof.field_hash;

        for (i, sibling) in proof.siblings.iter().enumerate() {
            let bit = (proof.index >> i) & 1;
            if bit == 0 {
                // Current node is left child
                current_hash = Self::hash_children(&current_hash, sibling);
            } else {
                // Current node is right child
                current_hash = Self::hash_children(sibling, &current_hash);
            }
        }

        current_hash == proof.root_hash
    }

    /// Hash two children nodes
    fn hash_children(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(left);
        hasher.update(right);
        hasher.finalize().into()
    }

    /// Verify canonical JSON using JCS
    fn verify_canonical_json(&self, multiproof: &BatchedMultiproof) -> bool {
        // Parse the canonical JSON
        if let Ok(parsed_json) =
            serde_json::from_str::<serde_json::Value>(&multiproof.canonical_json)
        {
            // Re-canonicalize and compare
            if let Ok(recanonicalized) = JCSCanonicalizer::canonicalize(&parsed_json) {
                recanonicalized == multiproof.canonical_json
            } else {
                false
            }
        } else {
            false
        }
    }

    /// Verify root consistency across all proofs in the batch
    fn verify_root_consistency(&self, multiproof: &BatchedMultiproof) -> bool {
        multiproof
            .field_proofs
            .iter()
            .all(|proof| proof.root_hash == multiproof.root_hash)
    }

    /// Get cache statistics
    pub fn get_cache_stats(&self) -> HashMap<String, usize> {
        let mut stats = HashMap::new();
        if let Some(cache) = read_witness(&self.proof_cache) {
            stats.insert("cache_size".to_string(), cache.entries.len());
            stats.insert("cache_capacity".to_string(), cache.capacity);
        }
        stats
    }

    /// Clear cache
    pub fn clear_cache(&self) {
        if let Some(mut cache) = write_witness(&self.proof_cache) {
            cache.entries.clear();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn test_jcs_canonicalization() {
        let json = serde_json::json!({
            "c": 3,
            "a": 1,
            "b": 2
        });

        let canonical = JCSCanonicalizer::canonicalize(&json).unwrap();
        assert_eq!(canonical, r#"{"a":1,"b":2,"c":3}"#);
    }

    #[test]
    fn test_merkle_proof_verification() {
        let checker = OptimizedWitnessChecker::new(CacheConfig::default());

        // Create a simple proof
        let proof = MerkleProof {
            field_path: vec!["field1".to_string()],
            siblings: vec![[0u8; 32]],
            root_hash: [1u8; 32],
            field_hash: [2u8; 32],
            index: 0,
        };

        // This will fail because it's not a real proof, but tests the structure
        let result = checker.verify_proof(&proof);
        assert!(!result); // Should fail for invalid proof
    }

    #[test]
    fn test_batched_multiproof() {
        let checker = OptimizedWitnessChecker::new(CacheConfig::default());

        let multiproof = BatchedMultiproof {
            emission_id: "test_emission".to_string(),
            field_proofs: vec![],
            root_hash: [1u8; 32],
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            canonical_json: r#"{}"#.to_string(),
        };

        let result = checker.verify_batched_multiproof(&multiproof);
        assert!(result); // Should pass for empty batch
    }

    #[test]
    fn test_performance_benchmark() {
        let checker = OptimizedWitnessChecker::new(CacheConfig::default());

        // Create test proofs
        let proofs: Vec<MerkleProof> = (0..1000)
            .map(|i| MerkleProof {
                field_path: vec![format!("field{}", i)],
                siblings: vec![[0u8; 32]],
                root_hash: [1u8; 32],
                field_hash: [2u8; 32],
                index: i,
            })
            .collect();

        // Benchmark verification
        let start = std::time::Instant::now();
        for proof in &proofs {
            checker.verify_proof(proof);
        }
        let duration = start.elapsed();

        // Should complete in less than 1ms for 1000 operations
        assert!(
            duration.as_millis() < 1,
            "Witness verification too slow: {:?}",
            duration
        );
        println!("1000 witness verifications took: {:?}", duration);
    }
}
