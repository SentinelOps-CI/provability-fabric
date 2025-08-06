use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

/// Near-duplicate detection result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NearDupeDetection {
    pub similarity_score: f64,
    pub matched_content: String,
    pub content_hash: String,
}

/// Near-duplicate detector using MinHash and Bloom filters
pub struct NearDupeDetector {
    known_hashes: HashMap<String, String>,
    shingle_size: usize,
    num_hashes: usize,
}

impl NearDupeDetector {
    pub fn new() -> Self {
        Self {
            known_hashes: HashMap::new(),
            shingle_size: 3,
            num_hashes: 128,
        }
    }

    /// Add known content to the detector
    pub fn add_known_content(&mut self, content: &str, identifier: String) {
        let content_hash = self.compute_minhash(content);
        self.known_hashes.insert(content_hash, identifier);
    }

    /// Detect near-duplicates in text
    pub fn detect(&self, text: &str) -> Option<NearDupeDetection> {
        let text_hash = self.compute_minhash(text);

        let mut best_match: Option<(f64, String, String)> = None;

        for (known_hash, identifier) in &self.known_hashes {
            let similarity = self.compute_similarity(&text_hash, known_hash);

            if similarity > 0.7 {
                // Threshold for near-duplicate
                match &best_match {
                    Some((best_sim, _, _)) if similarity > *best_sim => {
                        best_match = Some((similarity, identifier.clone(), known_hash.clone()));
                    }
                    None => {
                        best_match = Some((similarity, identifier.clone(), known_hash.clone()));
                    }
                    _ => {}
                }
            }
        }

        if let Some((similarity, matched_content, content_hash)) = best_match {
            Some(NearDupeDetection {
                similarity_score: similarity,
                matched_content,
                content_hash,
            })
        } else {
            None
        }
    }

    /// Compute MinHash signature for text
    fn compute_minhash(&self, text: &str) -> String {
        let shingles = self.create_shingles(text);
        let mut min_hashes = vec![u64::MAX; self.num_hashes];

        for shingle in shingles {
            for i in 0..self.num_hashes {
                let hash_value = self.hash_shingle_with_seed(&shingle, i as u64);
                if hash_value < min_hashes[i] {
                    min_hashes[i] = hash_value;
                }
            }
        }

        // Convert to string representation
        min_hashes
            .iter()
            .map(|h| format!("{:x}", h))
            .collect::<Vec<_>>()
            .join(",")
    }

    /// Create character shingles from text
    fn create_shingles(&self, text: &str) -> Vec<String> {
        let normalized = text
            .to_lowercase()
            .chars()
            .filter(|c| c.is_alphanumeric())
            .collect::<String>();

        if normalized.len() < self.shingle_size {
            return vec![normalized];
        }

        let mut shingles = Vec::new();
        for i in 0..=normalized.len() - self.shingle_size {
            let shingle = normalized[i..i + self.shingle_size].to_string();
            shingles.push(shingle);
        }

        shingles
    }

    /// Hash shingle with seed for different hash functions
    fn hash_shingle_with_seed(&self, shingle: &str, seed: u64) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        seed.hash(&mut hasher);
        shingle.hash(&mut hasher);
        hasher.finish()
    }

    /// Compute Jaccard similarity between two MinHash signatures
    fn compute_similarity(&self, hash1: &str, hash2: &str) -> f64 {
        let hashes1: Vec<&str> = hash1.split(',').collect();
        let hashes2: Vec<&str> = hash2.split(',').collect();

        if hashes1.len() != hashes2.len() {
            return 0.0;
        }

        let matching = hashes1
            .iter()
            .zip(hashes2.iter())
            .filter(|(h1, h2)| h1 == h2)
            .count();

        matching as f64 / hashes1.len() as f64
    }

    /// Check if text is memorized content
    pub fn is_memorized(&self, text: &str, threshold: f64) -> bool {
        if let Some(detection) = self.detect(text) {
            detection.similarity_score > threshold
        } else {
            false
        }
    }

    /// Get similarity threshold for different risk levels
    pub fn get_threshold(risk_level: &str) -> f64 {
        match risk_level {
            "strict" => 0.5,
            "moderate" => 0.7,
            "lenient" => 0.85,
            _ => 0.7,
        }
    }
}

/// Bloom filter for approximate membership testing
pub struct BloomFilter {
    bit_array: Vec<bool>,
    size: usize,
    num_hashes: usize,
}

impl BloomFilter {
    pub fn new(size: usize, num_hashes: usize) -> Self {
        Self {
            bit_array: vec![false; size],
            size,
            num_hashes,
        }
    }

    /// Add item to bloom filter
    pub fn add(&mut self, item: &str) {
        for i in 0..self.num_hashes {
            let hash = self.hash_with_seed(item, i as u64);
            let index = (hash as usize) % self.size;
            self.bit_array[index] = true;
        }
    }

    /// Check if item might be in the set
    pub fn might_contain(&self, item: &str) -> bool {
        for i in 0..self.num_hashes {
            let hash = self.hash_with_seed(item, i as u64);
            let index = (hash as usize) % self.size;
            if !self.bit_array[index] {
                return false;
            }
        }
        true
    }

    /// Hash with seed
    fn hash_with_seed(&self, item: &str, seed: u64) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        seed.hash(&mut hasher);
        item.hash(&mut hasher);
        hasher.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_shingle_creation() {
        let detector = NearDupeDetector::new();
        let text = "hello world";
        let shingles = detector.create_shingles(text);

        assert!(!shingles.is_empty());
        assert_eq!(shingles.len(), text.len() - detector.shingle_size + 1);
    }

    #[test]
    fn test_minhash_consistency() {
        let detector = NearDupeDetector::new();
        let text = "This is a test document";

        let hash1 = detector.compute_minhash(text);
        let hash2 = detector.compute_minhash(text);

        assert_eq!(hash1, hash2);
    }

    #[test]
    fn test_similarity_computation() {
        let detector = NearDupeDetector::new();
        let text1 = "This is a test document";
        let text2 = "This is a test document with extra words";
        let text3 = "Completely different content here";

        let hash1 = detector.compute_minhash(text1);
        let hash2 = detector.compute_minhash(text2);
        let hash3 = detector.compute_minhash(text3);

        let sim_12 = detector.compute_similarity(&hash1, &hash2);
        let sim_13 = detector.compute_similarity(&hash1, &hash3);

        assert!(sim_12 > sim_13);
        assert!(sim_12 > 0.3); // Similar texts should have decent similarity
    }

    #[test]
    fn test_near_duplicate_detection() {
        let mut detector = NearDupeDetector::new();

        // Add known content
        detector.add_known_content(
            "The quick brown fox jumps over the lazy dog",
            "test_content_1".to_string(),
        );

        // Test similar content
        let similar_text = "The quick brown fox jumps over a lazy dog";
        let detection = detector.detect(similar_text);

        assert!(detection.is_some());
        let detection = detection.unwrap();
        assert!(detection.similarity_score > 0.5);
    }

    #[test]
    fn test_bloom_filter() {
        let mut bloom = BloomFilter::new(1000, 3);

        bloom.add("test_item");
        assert!(bloom.might_contain("test_item"));

        // This might return true due to false positives, but should generally be false
        let false_positive_rate = (0..100)
            .map(|i| format!("non_existent_item_{}", i))
            .filter(|item| bloom.might_contain(item))
            .count() as f64
            / 100.0;

        assert!(false_positive_rate < 0.1); // Should be low false positive rate
    }

    #[test]
    fn test_memorization_check() {
        let mut detector = NearDupeDetector::new();
        detector.add_known_content("Exact memorized content", "memorized_1".to_string());

        // Exact match should be detected as memorized
        assert!(detector.is_memorized("Exact memorized content", 0.9));

        // Different content should not be memorized
        assert!(!detector.is_memorized("Completely different text", 0.9));
    }
}
