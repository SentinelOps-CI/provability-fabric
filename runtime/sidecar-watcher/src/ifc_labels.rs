// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::debug;

/// Label ID for efficient bitset operations
pub type LabelId = u32;

/// Prefix for label classification
pub type LabelPrefix = u32;

/// Optimized label structure with dense ID
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Label {
    pub id: LabelId,
    pub name: String,
    pub level: u32,
    pub categories: Vec<String>,
    pub tenant: String,
}

/// Legacy label structure for compatibility
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct LegacyLabel {
    pub name: String,
    pub level: u32,
    pub categories: Vec<String>,
    pub tenant: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowCheck {
    pub from_label: LegacyLabel,
    pub to_label: LegacyLabel,
    pub allowed: bool,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabeledData {
    pub data_id: String,
    pub label: LegacyLabel,
    pub witness_id: String,
    pub metadata: HashMap<String, String>,
}

/// Optimized IFC manager with bitset operations
pub struct OptimizedIFCManager {
    labels: HashMap<String, Label>,
    label_id_map: HashMap<LabelId, String>,
    next_label_id: LabelId,
    // Bitsets for fast AllowΔ operations
    allow_bitsets: [AllowRow; 128], // Bounded dense label domain, sparse prefixes
    // Precomputed joins for common operations
    join_cache: HashMap<(LabelId, LabelId), u128>,
    // Rate limiting for declassify operations
    declassify_limits: HashMap<LabelId, u32>,
}

// Every prefix follows the same representation. A single-entry row avoids
// hashing and allocation; rows with more prefixes retain sparse hash lookup.
enum AllowRow {
    Empty,
    Single(LabelPrefix, u128),
    Many(HashMap<LabelPrefix, u128>),
}

impl AllowRow {
    #[inline]
    fn get(&self, prefix: LabelPrefix) -> Option<u128> {
        match self {
            Self::Empty => None,
            Self::Single(key, bits) => (*key == prefix).then_some(*bits),
            Self::Many(map) => map.get(&prefix).copied(),
        }
    }

    #[inline]
    fn grant(&mut self, prefix: LabelPrefix, bit: u128) {
        match self {
            Self::Empty => *self = Self::Single(prefix, bit),
            Self::Single(key, bits) if *key == prefix => *bits |= bit,
            Self::Single(key, bits) => {
                let mut map = HashMap::new();
                map.insert(*key, *bits);
                map.insert(prefix, bit);
                *self = Self::Many(map);
            }
            Self::Many(map) => *map.entry(prefix).or_insert(0) |= bit,
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Empty => 0,
            Self::Single(..) => 1,
            Self::Many(map) => map.len(),
        }
    }
}

/// Legacy label manager for compatibility
pub struct LabelManager {
    labels: HashMap<String, LegacyLabel>,
    flow_policies: Vec<FlowPolicy>,
    labeled_data: HashMap<String, LabeledData>,
    witness_cache: HashMap<String, WitnessInfo>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowPolicy {
    pub from: String,
    pub to: String,
    pub allowed: bool,
    pub condition: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WitnessInfo {
    pub witness_id: String,
    pub path: Vec<String>,
    pub hash: String,
    pub timestamp: u64,
    pub valid: bool,
}

impl OptimizedIFCManager {
    /// Create new optimized IFC manager
    pub fn new() -> Result<Self> {
        let mut labels = HashMap::new();
        let mut label_id_map = HashMap::new();
        let mut next_label_id = 0;

        // Initialize default labels with dense IDs
        let default_labels = vec![
            ("public", 0, vec!["unclassified"]),
            ("internal", 1, vec!["internal"]),
            ("confidential", 2, vec!["confidential"]),
            ("secret", 3, vec!["secret"]),
        ];

        for (name, level, categories) in default_labels {
            let label = Label {
                id: next_label_id,
                name: name.to_string(),
                level,
                categories: categories.into_iter().map(|s| s.to_string()).collect(),
                tenant: "default".to_string(),
            };
            labels.insert(name.to_string(), label.clone());
            label_id_map.insert(next_label_id, name.to_string());
            next_label_id += 1;
        }

        Ok(Self {
            labels,
            label_id_map,
            next_label_id,
            allow_bitsets: std::array::from_fn(|_| AllowRow::Empty),
            join_cache: HashMap::new(),
            declassify_limits: HashMap::new(),
        })
    }

    /// Add a new label with automatic ID assignment
    pub fn add_label(
        &mut self,
        name: String,
        level: u32,
        categories: Vec<String>,
        tenant: String,
    ) -> LabelId {
        let id = self.next_label_id;
        let label = Label {
            id,
            name: name.clone(),
            level,
            categories,
            tenant,
        };
        self.labels.insert(name.clone(), label);
        self.label_id_map.insert(id, name);
        self.next_label_id += 1;
        id
    }

    /// Get label by name
    pub fn get_label(&self, name: &str) -> Option<&Label> {
        self.labels.get(name)
    }

    /// Get label by ID
    pub fn get_label_by_id(&self, id: LabelId) -> Option<&Label> {
        self.label_id_map
            .get(&id)
            .and_then(|name| self.labels.get(name))
    }

    /// Declassify from higher to lower label (hot path)
    #[inline(always)]
    pub fn declassify(
        &mut self,
        from_label: LabelId,
        to_label: LabelId,
        prefix: LabelPrefix,
    ) -> bool {
        // This records a previously authorized declassification; it does not
        // determine authorization. Reject IDs outside the supported bitset.
        let Some(bit) = 1u128.checked_shl(from_label) else { return false; };
        // IDs are assigned contiguously and never removed. Duplicate names
        // preserve the existing ID membership semantics.
        if from_label >= self.next_label_id || to_label >= self.next_label_id || to_label >= 128 {
            return false;
        }
        self.allow_bitsets[to_label as usize].grant(prefix, bit);
        true
    }

    /// Check if output is allowed (hot path)
    #[inline(always)]
    pub fn is_output_allowed(
        &self,
        label: LabelId,
        prefix: LabelPrefix,
        required_labels: &[LabelId],
    ) -> bool {
        if label >= 128 || label >= self.next_label_id {
            return false;
        }
        if let Some(allow_bitset) = self.allow_bitsets[label as usize].get(prefix) {
            // Check if all required labels are in the allow set
            for &required_label in required_labels {
                let Some(bit) = 1u128.checked_shl(required_label) else { return false; };
                if required_label >= self.next_label_id || allow_bitset & bit == 0 {
                    return false;
                }
            }
            true
        } else {
            // No allow bitset means no declassifications allowed
            required_labels.is_empty()
        }
    }

    /// Compute label join with caching
    #[inline(always)]
    pub fn join_labels(&mut self, label1: LabelId, label2: LabelId) -> LabelId {
        // Check cache first
        let cache_key = if label1 < label2 {
            (label1, label2)
        } else {
            (label2, label1)
        };
        if let Some(&cached_result) = self.join_cache.get(&cache_key) {
            return cached_result as LabelId;
        }

        // Compute join (simplified: take higher level)
        let result = if let (Some(label1_obj), Some(label2_obj)) =
            (self.get_label_by_id(label1), self.get_label_by_id(label2))
        {
            if label1_obj.level >= label2_obj.level {
                label1
            } else {
                label2
            }
        } else {
            label1 // Fallback
        };

        // Cache the result
        self.join_cache.insert(cache_key, result as u128);
        result
    }

    /// Precompute common joins for performance
    pub fn precompute_joins(&mut self) {
        let label_ids: Vec<LabelId> = self.label_id_map.keys().copied().collect();

        for &label1 in &label_ids {
            for &label2 in &label_ids {
                if label1 != label2 {
                    self.join_labels(label1, label2);
                }
            }
        }
    }

    /// Set declassify rate limit for a label
    pub fn set_declassify_limit(&mut self, label: LabelId, limit: u32) {
        self.declassify_limits.insert(label, limit);
    }

    /// Check declassify rate limit
    #[inline(always)]
    pub fn check_declassify_limit(&self, label: LabelId, current_count: u32) -> bool {
        self.declassify_limits
            .get(&label)
            .is_none_or(|&limit| current_count < limit)
    }

    /// Get allow bitset for debugging
    pub fn get_allow_bitset(&self, label: LabelId, prefix: LabelPrefix) -> Option<u128> {
        self.allow_bitsets.get(label as usize).and_then(|row| row.get(prefix))
    }

    /// Clear all declassifications (for testing)
    pub fn clear_declassifications(&mut self) {
        self.allow_bitsets = std::array::from_fn(|_| AllowRow::Empty);
    }

    /// Get statistics
    pub fn get_stats(&self) -> HashMap<String, usize> {
        let mut stats = HashMap::new();
        stats.insert("total_labels".to_string(), self.labels.len());
        stats.insert("allow_bitsets".to_string(), self.allow_bitsets.iter().map(AllowRow::len).sum());
        stats.insert("join_cache_entries".to_string(), self.join_cache.len());
        stats.insert(
            "declassify_limits".to_string(),
            self.declassify_limits.len(),
        );
        stats
    }
}

impl LabelManager {
    pub fn new() -> Result<Self> {
        let mut labels = HashMap::new();

        // Initialize default labels
        labels.insert(
            "public".to_string(),
            LegacyLabel {
                name: "public".to_string(),
                level: 0,
                categories: vec!["unclassified".to_string()],
                tenant: "default".to_string(),
            },
        );

        labels.insert(
            "internal".to_string(),
            LegacyLabel {
                name: "internal".to_string(),
                level: 1,
                categories: vec!["internal".to_string()],
                tenant: "default".to_string(),
            },
        );

        labels.insert(
            "confidential".to_string(),
            LegacyLabel {
                name: "confidential".to_string(),
                level: 2,
                categories: vec!["confidential".to_string()],
                tenant: "default".to_string(),
            },
        );

        labels.insert(
            "secret".to_string(),
            LegacyLabel {
                name: "secret".to_string(),
                level: 3,
                categories: vec!["secret".to_string()],
                tenant: "default".to_string(),
            },
        );

        // Default flow policies (allow upward flow, deny downward)
        let flow_policies = vec![
            FlowPolicy {
                from: "public".to_string(),
                to: "internal".to_string(),
                allowed: true,
                condition: None,
            },
            FlowPolicy {
                from: "public".to_string(),
                to: "confidential".to_string(),
                allowed: true,
                condition: None,
            },
            FlowPolicy {
                from: "public".to_string(),
                to: "secret".to_string(),
                allowed: true,
                condition: None,
            },
            FlowPolicy {
                from: "internal".to_string(),
                to: "confidential".to_string(),
                allowed: true,
                condition: None,
            },
            FlowPolicy {
                from: "internal".to_string(),
                to: "secret".to_string(),
                allowed: true,
                condition: None,
            },
            FlowPolicy {
                from: "confidential".to_string(),
                to: "secret".to_string(),
                allowed: true,
                condition: None,
            },
            // Deny downward flows
            FlowPolicy {
                from: "internal".to_string(),
                to: "public".to_string(),
                allowed: false,
                condition: None,
            },
            FlowPolicy {
                from: "confidential".to_string(),
                to: "public".to_string(),
                allowed: false,
                condition: None,
            },
            FlowPolicy {
                from: "confidential".to_string(),
                to: "internal".to_string(),
                allowed: false,
                condition: None,
            },
            FlowPolicy {
                from: "secret".to_string(),
                to: "public".to_string(),
                allowed: false,
                condition: None,
            },
            FlowPolicy {
                from: "secret".to_string(),
                to: "internal".to_string(),
                allowed: false,
                condition: None,
            },
            FlowPolicy {
                from: "secret".to_string(),
                to: "confidential".to_string(),
                allowed: false,
                condition: None,
            },
        ];

        Ok(Self {
            labels,
            flow_policies,
            labeled_data: HashMap::new(),
            witness_cache: HashMap::new(),
        })
    }

    pub fn attach_label(
        &mut self,
        data_id: String,
        label_name: String,
        witness_id: String,
    ) -> Result<()> {
        let label = self
            .labels
            .get(&label_name)
            .ok_or_else(|| anyhow::anyhow!("Unknown label: {}", label_name))?
            .clone();

        let labeled_data = LabeledData {
            data_id: data_id.clone(),
            label,
            witness_id: witness_id.clone(),
            metadata: HashMap::new(),
        };

        self.labeled_data.insert(data_id.clone(), labeled_data);
        debug!("Attached label {} to data {}", label_name, data_id);

        Ok(())
    }

    pub fn validate_witness(&mut self, witness_id: &str, path: Vec<String>) -> Result<bool> {
        // Check witness cache first
        if let Some(witness) = self.witness_cache.get(witness_id) {
            return Ok(witness.valid && witness.path == path);
        }

        // Validate new witness (simplified - in production would verify Merkle proofs)
        let valid = !path.is_empty() && path.iter().all(|p| !p.is_empty());

        let witness_info = WitnessInfo {
            witness_id: witness_id.to_string(),
            path: path.clone(),
            hash: format!("witness_{}", witness_id),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            valid,
        };

        self.witness_cache
            .insert(witness_id.to_string(), witness_info);

        debug!("Validated witness {}: {}", witness_id, valid);
        Ok(valid)
    }

    pub fn check_flow(&self, from_label: &str, to_label: &str) -> FlowCheck {
        // Find applicable flow policy
        for policy in &self.flow_policies {
            if policy.from == from_label && policy.to == to_label {
                let from_label_obj =
                    self.labels
                        .get(from_label)
                        .cloned()
                        .unwrap_or_else(|| LegacyLabel {
                            name: from_label.to_string(),
                            level: 0,
                            categories: vec![],
                            tenant: "unknown".to_string(),
                        });

                let to_label_obj =
                    self.labels
                        .get(to_label)
                        .cloned()
                        .unwrap_or_else(|| LegacyLabel {
                            name: to_label.to_string(),
                            level: 0,
                            categories: vec![],
                            tenant: "unknown".to_string(),
                        });

                return FlowCheck {
                    from_label: from_label_obj,
                    to_label: to_label_obj,
                    allowed: policy.allowed,
                    reason: if policy.allowed {
                        "Flow allowed by policy".to_string()
                    } else {
                        "Flow denied by policy".to_string()
                    },
                };
            }
        }

        // Default deny for unknown flows
        FlowCheck {
            from_label: LegacyLabel {
                name: from_label.to_string(),
                level: 0,
                categories: vec![],
                tenant: "unknown".to_string(),
            },
            to_label: LegacyLabel {
                name: to_label.to_string(),
                level: 0,
                categories: vec![],
                tenant: "unknown".to_string(),
            },
            allowed: false,
            reason: "No flow policy found - default deny".to_string(),
        }
    }

    pub fn get_data_label(&self, data_id: &str) -> Option<&LegacyLabel> {
        self.labeled_data.get(data_id).map(|ld| &ld.label)
    }

    pub fn update_flow_policies(&mut self, policies: Vec<FlowPolicy>) {
        self.flow_policies = policies;
        debug!("Updated flow policies: {} rules", self.flow_policies.len());
    }

    pub fn add_label(&mut self, label: LegacyLabel) {
        self.labels.insert(label.name.clone(), label);
    }

    pub fn get_label_stats(&self) -> HashMap<String, u32> {
        let mut stats = HashMap::new();

        for labeled_data in self.labeled_data.values() {
            let count = stats.entry(labeled_data.label.name.clone()).or_insert(0);
            *count += 1;
        }

        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_optimized_ifc_creation() {
        let manager = OptimizedIFCManager::new().unwrap();
        assert_eq!(manager.labels.len(), 4); // public, internal, confidential, secret
        assert_eq!(manager.next_label_id, 4);
    }

    #[test]
    fn test_declassify_operation() {
        let mut manager = OptimizedIFCManager::new().unwrap();

        // Get label IDs
        let secret_id = manager.get_label("secret").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;

        // Declassify from secret to internal
        let result = manager.declassify(secret_id, internal_id, 0);
        assert!(result);

        // Check that the bitset was updated
        let bitset = manager.get_allow_bitset(internal_id, 0).unwrap();
        assert!(bitset & (1u128 << secret_id) != 0);
    }

    #[test]
    fn test_output_allowed_check() {
        let mut manager = OptimizedIFCManager::new().unwrap();

        let secret_id = manager.get_label("secret").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;

        // Declassify from secret to internal
        manager.declassify(secret_id, internal_id, 0);

        // Check that output is allowed
        let required_labels = vec![secret_id];
        let allowed = manager.is_output_allowed(internal_id, 0, &required_labels);
        assert!(allowed);

        // Check that output is not allowed without declassification
        let not_allowed = manager.is_output_allowed(internal_id, 1, &required_labels);
        assert!(!not_allowed);
    }

    #[test]
    fn test_invalid_label_ids_do_not_grant_or_panic() {
        let mut manager = OptimizedIFCManager::new().unwrap();
        let internal = manager.get_label("internal").unwrap().id;
        let secret = manager.get_label("secret").unwrap().id;
        assert!(!manager.declassify(128, internal, 0));
        assert!(!manager.declassify(secret, 128, 0));
        assert!(!manager.declassify(100, internal, 0));
        assert!(!manager.is_output_allowed(128, 0, &[]));
        assert!(manager.declassify(secret, internal, 0));
        assert!(!manager.is_output_allowed(internal, 0, &[128]));
        assert!(manager.is_output_allowed(internal, 0, &[secret]));
    }

    #[test]
    fn test_label_join_caching() {
        let mut manager = OptimizedIFCManager::new().unwrap();

        let public_id = manager.get_label("public").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;

        // First join should compute and cache
        let join1 = manager.join_labels(public_id, internal_id);
        assert_eq!(join1, internal_id); // Higher level wins

        // Second join should use cache
        let join2 = manager.join_labels(internal_id, public_id);
        assert_eq!(join2, internal_id);

        // Check that cache was populated
        let stats = manager.get_stats();
        assert!(stats["join_cache_entries"] > 0);
    }

    #[test]
    fn test_declassify_rate_limiting() {
        let mut manager = OptimizedIFCManager::new().unwrap();

        let internal_id = manager.get_label("internal").unwrap().id;
        manager.set_declassify_limit(internal_id, 5);

        // Should allow within limit
        assert!(manager.check_declassify_limit(internal_id, 3));

        // Should deny over limit
        assert!(!manager.check_declassify_limit(internal_id, 6));
    }

    #[test]
    fn test_allow_rows_match_sparse_reference_across_prefixes_and_clear() {
        let mut manager = OptimizedIFCManager::new().unwrap();
        // Add labels including the final representable bit and the first
        // unsupported bit. Retain duplicate-name membership behavior.
        for n in 4..=128 {
            manager.add_label(format!("label-{n}"), n, vec![], "tenant".into());
        }
        manager.add_label("label-4".into(), 4, vec![], "tenant".into());
        let mut reference: HashMap<(LabelId, LabelPrefix), u128> = HashMap::new();
        for from in [0, 1, 4, 127, 128, u32::MAX] {
            for to in [0, 1, 4, 127, 128, u32::MAX] {
                for prefix in [0, 7, 99, u32::MAX] {
                    let expected = from < 128 && to < 128;
                    assert_eq!(manager.declassify(from, to, prefix), expected);
                    if expected {
                        *reference.entry((to, prefix)).or_insert(0) |= 1u128 << from;
                    }
                    assert_eq!(manager.get_allow_bitset(to, prefix), reference.get(&(to,prefix)).copied());
                }
            }
        }
        for to in [0, 1, 4, 127, 128, u32::MAX] {
            for prefix in [0, 7, 99, 123, u32::MAX] {
                for required in [vec![], vec![0], vec![127], vec![0, 4, 127], vec![128]] {
                    let bits = reference.get(&(to,prefix)).copied().unwrap_or(0);
                    let expected = to < 128 && required.iter().all(|&id| {
                        1u128.checked_shl(id).is_some_and(|bit| bits & bit != 0)
                    });
                    assert_eq!(manager.is_output_allowed(to,prefix,&required), expected);
                }
            }
        }
        assert_eq!(manager.get_stats()["allow_bitsets"], reference.len());
        manager.clear_declassifications();
        assert_eq!(manager.get_stats()["allow_bitsets"], 0);
        assert!(!manager.is_output_allowed(1,7,&[0]));
        assert!(manager.is_output_allowed(1,7,&[]));
    }

    #[test]
    fn test_performance_benchmark() {
        let mut manager = OptimizedIFCManager::new().unwrap();

        // Precompute joins for performance
        manager.precompute_joins();

        let secret_id = manager.get_label("secret").unwrap().id;
        let internal_id = manager.get_label("internal").unwrap().id;
        let _public_id = manager.get_label("public").unwrap().id;

        // Benchmark declassify operations
        let start = std::time::Instant::now();
        for _ in 0..100_000 {
            assert!(manager.declassify(std::hint::black_box(secret_id), internal_id, 0));
        }
        let duration = start.elapsed();

        if !cfg!(debug_assertions) {
            assert!(duration.as_millis() < 1, "Declassify too slow: {:?}", duration);
        }
        println!("100k declassify operations took: {:?}", duration);

        // Benchmark output allowed checks
        let start = std::time::Instant::now();
        let required_labels = vec![secret_id];
        for _ in 0..100_000 {
            assert!(manager.is_output_allowed(internal_id, 0, std::hint::black_box(&required_labels)));
        }
        let duration = start.elapsed();

        if !cfg!(debug_assertions) {
            assert!(duration.as_millis() < 1, "Output check too slow: {:?}", duration);
        }
        println!("100k output checks took: {:?}", duration);
    }

    #[test]
    fn test_legacy_compatibility() {
        let legacy_manager = LabelManager::new().unwrap();

        // Test legacy functionality still works
        let public_label = legacy_manager.labels.get("public").unwrap();
        assert_eq!(public_label.name, "public");
        assert_eq!(public_label.level, 0);

        // Test flow check
        let flow_check = legacy_manager.check_flow("public", "internal");
        assert!(flow_check.allowed);

        let reverse_flow = legacy_manager.check_flow("internal", "public");
        assert!(!reverse_flow.allowed);
    }
}
