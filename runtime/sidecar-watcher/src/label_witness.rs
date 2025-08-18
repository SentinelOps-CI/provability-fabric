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
use std::collections::HashMap;
use std::error::Error;

/// Merkle tree node for witness verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MerkleNode {
    Leaf {
        path: String,
        hash: String,
        value_hash: String,
    },
    Internal {
        left: Box<MerkleNode>,
        right: Box<MerkleNode>,
        hash: String,
    },
}

/// Bloom filter witness
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BloomWitness {
    pub paths: Vec<String>,
    pub hash_functions: Vec<u64>,
    pub filter: Vec<bool>,
    pub size: usize,
    pub hash_count: usize,
}

/// Witness verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessVerificationResult {
    pub valid: bool,
    pub merkle_valid: bool,
    pub bloom_valid: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

/// Label witness verifier
pub struct LabelWitnessVerifier {
    merkle_root: Option<String>,
    bloom_witness: Option<BloomWitness>,
    strict_mode: bool,
}

impl LabelWitnessVerifier {
    /// Create new verifier
    pub fn new() -> Self {
        Self {
            merkle_root: None,
            bloom_witness: None,
            strict_mode: true,
        }
    }

    /// Set Merkle root for verification
    pub fn with_merkle_root(mut self, root: String) -> Self {
        self.merkle_root = Some(root);
        self
    }

    /// Set Bloom witness for verification
    pub fn with_bloom_witness(mut self, witness: BloomWitness) -> Self {
        self.bloom_witness = Some(witness);
        self
    }

    /// Set strict mode
    pub fn with_strict_mode(mut self, strict: bool) -> Self {
        self.strict_mode = strict;
        self
    }

    /// Verify Merkle witness
    pub fn verify_merkle_witness(
        &self,
        proof: &MerkleNode,
        path: &str,
        expected_hash: &str,
    ) -> Result<bool, String> {
        match proof {
            MerkleNode::Leaf {
                path: p, hash: h, ..
            } => {
                if p == path && h == expected_hash {
                    Ok(true)
                } else {
                    Err(format!(
                        "Merkle leaf mismatch: expected path '{}' hash '{}', got '{}' '{}'",
                        path, expected_hash, p, h
                    ))
                }
            }
            MerkleNode::Internal {
                left,
                right,
                hash: h,
            } => {
                // Verify internal node hash
                let computed_hash = self.compute_internal_hash(left, right)?;
                if computed_hash != *h {
                    return Err(format!(
                        "Invalid internal node hash: expected '{}', computed '{}'",
                        h, computed_hash
                    ));
                }

                // Recursively verify left and right subtrees
                let left_valid = self.verify_merkle_witness(left, path, expected_hash)?;
                let right_valid = self.verify_merkle_witness(right, path, expected_hash)?;

                Ok(left_valid || right_valid)
            }
        }
    }

    /// Compute hash for internal node
    fn compute_internal_hash(
        &self,
        left: &MerkleNode,
        right: &MerkleNode,
    ) -> Result<String, String> {
        let left_hash = match left {
            MerkleNode::Leaf { hash, .. } => hash.clone(),
            MerkleNode::Internal { hash, .. } => hash.clone(),
        };

        let right_hash = match right {
            MerkleNode::Leaf { hash, .. } => hash.clone(),
            MerkleNode::Internal { hash, .. } => hash.clone(),
        };

        let mut hasher = Sha256::new();
        hasher.update(left_hash.as_bytes());
        hasher.update(right_hash.as_bytes());
        Ok(format!("{:x}", hasher.finalize()))
    }

    /// Verify Bloom witness
    pub fn verify_bloom_witness(&self, witness: &BloomWitness, path: &str) -> Result<bool, String> {
        if witness.filter.is_empty() {
            return Err("Empty Bloom filter".to_string());
        }

        // Check if path is in Bloom filter
        let path_hashes = self.compute_bloom_hashes(path, witness.hash_count);
        let indices: Vec<usize> = path_hashes
            .iter()
            .map(|h| (*h % witness.size as u64) as usize)
            .collect();

        // All hash indices must be set to true
        let is_present = indices
            .iter()
            .all(|&idx| idx < witness.filter.len() && witness.filter[idx]);

        if is_present {
            // Check if path is in the known paths list
            if witness.paths.contains(&path.to_string()) {
                Ok(true)
            } else {
                // False positive - this is expected with Bloom filters
                Ok(false)
            }
        } else {
            Ok(false)
        }
    }

    /// Compute Bloom filter hashes for a path
    fn compute_bloom_hashes(&self, path: &str, hash_count: usize) -> Vec<u64> {
        let mut hashes = Vec::new();

        for i in 0..hash_count {
            let mut hasher = Sha256::new();
            hasher.update(path.as_bytes());
            hasher.update(i.to_string().as_bytes());
            let hash_bytes = hasher.finalize();

            // Convert first 8 bytes to u64
            let hash_u64 = u64::from_le_bytes([
                hash_bytes[0],
                hash_bytes[1],
                hash_bytes[2],
                hash_bytes[3],
                hash_bytes[4],
                hash_bytes[5],
                hash_bytes[6],
                hash_bytes[7],
            ]);

            hashes.push(hash_u64);
        }

        hashes
    }

    /// Verify complete witness
    pub fn verify_witness(
        &self,
        path: &str,
        merkle_proof: Option<&MerkleNode>,
        expected_hash: Option<&str>,
    ) -> WitnessVerificationResult {
        let mut result = WitnessVerificationResult {
            valid: true,
            merkle_valid: false,
            bloom_valid: false,
            errors: Vec::new(),
            warnings: Vec::new(),
        };

        // Verify Merkle witness if provided
        if let (Some(proof), Some(hash)) = (merkle_proof, expected_hash) {
            match self.verify_merkle_witness(proof, path, hash) {
                Ok(valid) => {
                    result.merkle_valid = valid;
                    if !valid {
                        result.errors.push(format!(
                            "Merkle witness verification failed for path '{}'",
                            path
                        ));
                        result.valid = false;
                    }
                }
                Err(e) => {
                    result.errors.push(format!(
                        "Merkle witness verification error for path '{}': {}",
                        path, e
                    ));
                    result.valid = false;
                }
            }
        } else if self.strict_mode && self.merkle_root.is_some() {
            result.errors.push(format!(
                "Merkle witness required but not provided for path '{}'",
                path
            ));
            result.valid = false;
        }

        // Verify Bloom witness if provided
        if let Some(witness) = &self.bloom_witness {
            match self.verify_bloom_witness(witness, path) {
                Ok(valid) => {
                    result.bloom_valid = valid;
                    if !valid {
                        result.warnings.push(format!(
                            "Bloom witness verification failed for path '{}'",
                            path
                        ));
                        // Bloom filter failures are warnings, not errors
                    }
                }
                Err(e) => {
                    result.warnings.push(format!(
                        "Bloom witness verification error for path '{}': {}",
                        path, e
                    ));
                }
            }
        }

        result
    }

    /// Verify multiple paths with witnesses
    pub fn verify_paths(
        &self,
        paths_with_witnesses: &[(String, Option<MerkleNode>, Option<String>)],
    ) -> Vec<WitnessVerificationResult> {
        paths_with_witnesses
            .iter()
            .map(|(path, merkle_proof, expected_hash)| {
                self.verify_witness(path, merkle_proof.as_ref(), expected_hash.as_deref())
            })
            .collect()
    }

    /// Check if all verifications passed
    pub fn all_valid(&self, results: &[WitnessVerificationResult]) -> bool {
        results.iter().all(|r| r.valid)
    }

    /// Get summary of verification results
    pub fn get_summary(&self, results: &[WitnessVerificationResult]) -> HashMap<String, usize> {
        let mut summary = HashMap::new();
        summary.insert("total".to_string(), results.len());
        summary.insert(
            "valid".to_string(),
            results.iter().filter(|r| r.valid).count(),
        );
        summary.insert(
            "invalid".to_string(),
            results.iter().filter(|r| !r.valid).count(),
        );
        summary.insert(
            "merkle_valid".to_string(),
            results.iter().filter(|r| r.merkle_valid).count(),
        );
        summary.insert(
            "bloom_valid".to_string(),
            results.iter().filter(|r| r.bloom_valid).count(),
        );
        summary.insert(
            "errors".to_string(),
            results.iter().map(|r| r.errors.len()).sum(),
        );
        summary.insert(
            "warnings".to_string(),
            results.iter().map(|r| r.warnings.len()).sum(),
        );
        summary
    }
}

/// Generate Merkle tree from labeled paths
pub fn generate_merkle_tree(labeled_paths: &HashMap<String, String>) -> Result<MerkleNode, String> {
    if labeled_paths.is_empty() {
        return Err("No labeled paths provided".to_string());
    }

    let mut leaves: Vec<MerkleNode> = labeled_paths
        .iter()
        .map(|(path, label)| {
            let mut hasher = Sha256::new();
            hasher.update(path.as_bytes());
            hasher.update(label.as_bytes());
            let value_hash = format!("{:x}", hasher.finalize());

            let mut hasher = Sha256::new();
            hasher.update(path.as_bytes());
            hasher.update(&value_hash.as_bytes());
            let hash = format!("{:x}", hasher.finalize());

            MerkleNode::Leaf {
                path: path.clone(),
                hash,
                value_hash,
            }
        })
        .collect();

    // Sort leaves for deterministic tree
    leaves.sort_by_key(|leaf| match leaf {
        MerkleNode::Leaf { path, .. } => path.clone(),
        _ => unreachable!(),
    });

    // Build tree bottom-up
    while leaves.len() > 1 {
        let mut new_level = Vec::new();

        for chunk in leaves.chunks(2) {
            if chunk.len() == 2 {
                let left = chunk[0].clone();
                let right = chunk[1].clone();

                let mut hasher = Sha256::new();
                match (&left, &right) {
                    (MerkleNode::Leaf { hash: lh, .. }, MerkleNode::Leaf { hash: rh, .. }) => {
                        hasher.update(lh.as_bytes());
                        hasher.update(rh.as_bytes());
                    }
                    _ => return Err("Invalid leaf structure".to_string()),
                }

                let hash = format!("{:x}", hasher.finalize());

                new_level.push(MerkleNode::Internal {
                    left: Box::new(left),
                    right: Box::new(right),
                    hash,
                });
            } else {
                // Single leaf, promote to next level
                new_level.push(chunk[0].clone());
            }
        }

        leaves = new_level;
    }

    leaves
        .pop()
        .ok_or("Failed to build Merkle tree".to_string())
}

/// Generate Bloom filter from labeled paths
pub fn generate_bloom_filter(
    labeled_paths: &HashMap<String, String>,
    size: usize,
    hash_count: usize,
) -> Result<BloomWitness, String> {
    if labeled_paths.is_empty() {
        return Err("No labeled paths provided".to_string());
    }

    let mut filter = vec![false; size];
    let paths: Vec<String> = labeled_paths.keys().cloned().collect();

    for path in &paths {
        let hashes = compute_bloom_hashes_for_path(path, hash_count);
        for hash in hashes {
            let index = (hash % size as u64) as usize;
            filter[index] = true;
        }
    }

    Ok(BloomWitness {
        paths,
        hash_functions: (0..hash_count).map(|i| i as u64).collect(),
        filter,
        size,
        hash_count,
    })
}

/// Compute Bloom filter hashes for a specific path
fn compute_bloom_hashes_for_path(path: &str, hash_count: usize) -> Vec<u64> {
    let mut hashes = Vec::new();

    for i in 0..hash_count {
        let mut hasher = Sha256::new();
        hasher.update(path.as_bytes());
        hasher.update(i.to_string().as_bytes());
        let hash_bytes = hasher.finalize();

        let hash_u64 = u64::from_le_bytes([
            hash_bytes[0],
            hash_bytes[1],
            hash_bytes[2],
            hash_bytes[3],
            hash_bytes[4],
            hash_bytes[5],
            hash_bytes[6],
            hash_bytes[7],
        ]);

        hashes.push(hash_u64);
    }

    hashes
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_merkle_tree_generation() {
        let mut labeled_paths = HashMap::new();
        labeled_paths.insert("$.user.password".to_string(), "secret".to_string());
        labeled_paths.insert("$.user.email".to_string(), "confidential".to_string());

        let tree = generate_merkle_tree(&labeled_paths).unwrap();

        match tree {
            MerkleNode::Internal { hash, .. } => {
                assert!(!hash.is_empty());
            }
            _ => panic!("Expected internal node"),
        }
    }

    #[test]
    fn test_bloom_filter_generation() {
        let mut labeled_paths = HashMap::new();
        labeled_paths.insert("$.user.password".to_string(), "secret".to_string());
        labeled_paths.insert("$.user.email".to_string(), "confidential".to_string());

        let bloom = generate_bloom_filter(&labeled_paths, 100, 5).unwrap();

        assert_eq!(bloom.size, 100);
        assert_eq!(bloom.hash_count, 5);
        assert_eq!(bloom.paths.len(), 2);
        assert_eq!(bloom.filter.len(), 100);
    }

    #[test]
    fn test_witness_verification() {
        let mut labeled_paths = HashMap::new();
        labeled_paths.insert("$.user.password".to_string(), "secret".to_string());

        let merkle_tree = generate_merkle_tree(&labeled_paths).unwrap();
        let bloom_witness = generate_bloom_filter(&labeled_paths, 100, 5).unwrap();

        let verifier = LabelWitnessVerifier::new().with_bloom_witness(bloom_witness);

        let result =
            verifier.verify_witness("$.user.password", Some(&merkle_tree), Some("expected_hash"));

        // Should have errors since expected_hash doesn't match
        assert!(!result.valid);
        assert!(!result.merkle_valid);
    }

    #[test]
    fn test_bloom_witness_verification() {
        let mut labeled_paths = HashMap::new();
        labeled_paths.insert("$.user.password".to_string(), "secret".to_string());

        let bloom_witness = generate_bloom_filter(&labeled_paths, 100, 5).unwrap();
        let verifier = LabelWitnessVerifier::new().with_bloom_witness(bloom_witness.clone());

        let result = verifier
            .verify_bloom_witness(&bloom_witness, "$.user.password")
            .unwrap();
        assert!(result);

        let result = verifier
            .verify_bloom_witness(&bloom_witness, "$.unknown.path")
            .unwrap();
        assert!(!result);
    }

    #[test]
    fn test_verification_summary() {
        let mut labeled_paths = HashMap::new();
        labeled_paths.insert("$.user.password".to_string(), "secret".to_string());
        labeled_paths.insert("$.user.email".to_string(), "confidential".to_string());

        let merkle_tree = generate_merkle_tree(&labeled_paths).unwrap();
        let bloom_witness = generate_bloom_filter(&labeled_paths, 100, 5).unwrap();

        let verifier = LabelWitnessVerifier::new().with_bloom_witness(bloom_witness);

        let paths_with_witnesses = vec![
            (
                "$.user.password".to_string(),
                Some(merkle_tree.clone()),
                Some("hash1".to_string()),
            ),
            (
                "$.user.email".to_string(),
                Some(merkle_tree),
                Some("hash2".to_string()),
            ),
        ];

        let results = verifier.verify_paths(&paths_with_witnesses);
        let summary = verifier.get_summary(&results);

        assert_eq!(summary["total"], 2);
        assert_eq!(summary["invalid"], 2); // Both should fail due to hash mismatch
        assert_eq!(summary["errors"], 2);
    }
}
