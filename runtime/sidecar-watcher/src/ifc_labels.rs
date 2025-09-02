// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tracing::{debug, warn};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct Label {
    pub name: String,
    pub level: u32,
    pub categories: Vec<String>,
    pub tenant: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowCheck {
    pub from_label: Label,
    pub to_label: Label,
    pub allowed: bool,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabeledData {
    pub data_id: String,
    pub label: Label,
    pub witness_id: String,
    pub metadata: HashMap<String, String>,
}

pub struct LabelManager {
    labels: HashMap<String, Label>,
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

impl LabelManager {
    pub fn new() -> Result<Self> {
        let mut labels = HashMap::new();
        
        // Initialize default labels
        labels.insert("public".to_string(), Label {
            name: "public".to_string(),
            level: 0,
            categories: vec!["unclassified".to_string()],
            tenant: "default".to_string(),
        });
        
        labels.insert("internal".to_string(), Label {
            name: "internal".to_string(),
            level: 1,
            categories: vec!["internal".to_string()],
            tenant: "default".to_string(),
        });
        
        labels.insert("confidential".to_string(), Label {
            name: "confidential".to_string(),
            level: 2,
            categories: vec!["confidential".to_string()],
            tenant: "default".to_string(),
        });
        
        labels.insert("secret".to_string(), Label {
            name: "secret".to_string(),
            level: 3,
            categories: vec!["secret".to_string()],
            tenant: "default".to_string(),
        });

        // Default flow policies (allow upward flow, deny downward)
        let flow_policies = vec![
            FlowPolicy { from: "public".to_string(), to: "internal".to_string(), allowed: true, condition: None },
            FlowPolicy { from: "public".to_string(), to: "confidential".to_string(), allowed: true, condition: None },
            FlowPolicy { from: "public".to_string(), to: "secret".to_string(), allowed: true, condition: None },
            FlowPolicy { from: "internal".to_string(), to: "confidential".to_string(), allowed: true, condition: None },
            FlowPolicy { from: "internal".to_string(), to: "secret".to_string(), allowed: true, condition: None },
            FlowPolicy { from: "confidential".to_string(), to: "secret".to_string(), allowed: true, condition: None },
            // Deny downward flows
            FlowPolicy { from: "internal".to_string(), to: "public".to_string(), allowed: false, condition: None },
            FlowPolicy { from: "confidential".to_string(), to: "public".to_string(), allowed: false, condition: None },
            FlowPolicy { from: "confidential".to_string(), to: "internal".to_string(), allowed: false, condition: None },
            FlowPolicy { from: "secret".to_string(), to: "public".to_string(), allowed: false, condition: None },
            FlowPolicy { from: "secret".to_string(), to: "internal".to_string(), allowed: false, condition: None },
            FlowPolicy { from: "secret".to_string(), to: "confidential".to_string(), allowed: false, condition: None },
        ];

        Ok(Self {
            labels,
            flow_policies,
            labeled_data: HashMap::new(),
            witness_cache: HashMap::new(),
        })
    }

    pub fn attach_label(&mut self, data_id: String, label_name: String, witness_id: String) -> Result<()> {
        let label = self.labels.get(&label_name)
            .ok_or_else(|| anyhow::anyhow!("Unknown label: {}", label_name))?
            .clone();

        let labeled_data = LabeledData {
            data_id: data_id.clone(),
            label,
            witness_id: witness_id.clone(),
            metadata: HashMap::new(),
        };

        self.labeled_data.insert(data_id, labeled_data);
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

        self.witness_cache.insert(witness_id.to_string(), witness_info);
        
        debug!("Validated witness {}: {}", witness_id, valid);
        Ok(valid)
    }

    pub fn check_flow(&self, from_label: &str, to_label: &str) -> FlowCheck {
        // Find applicable flow policy
        for policy in &self.flow_policies {
            if policy.from == from_label && policy.to == to_label {
                let from_label_obj = self.labels.get(from_label).cloned()
                    .unwrap_or_else(|| Label {
                        name: from_label.to_string(),
                        level: 0,
                        categories: vec![],
                        tenant: "unknown".to_string(),
                    });
                
                let to_label_obj = self.labels.get(to_label).cloned()
                    .unwrap_or_else(|| Label {
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
            from_label: Label { name: from_label.to_string(), level: 0, categories: vec![], tenant: "unknown".to_string() },
            to_label: Label { name: to_label.to_string(), level: 0, categories: vec![], tenant: "unknown".to_string() },
            allowed: false,
            reason: "No flow policy found - default deny".to_string(),
        }
    }

    pub fn get_data_label(&self, data_id: &str) -> Option<&Label> {
        self.labeled_data.get(data_id).map(|ld| &ld.label)
    }

    pub fn update_flow_policies(&mut self, policies: Vec<FlowPolicy>) {
        self.flow_policies = policies;
        debug!("Updated flow policies: {} rules", self.flow_policies.len());
    }

    pub fn add_label(&mut self, label: Label) {
        self.labels.insert(label.name.clone(), label);
    }

    pub fn get_label_stats(&self) -> HashMap<String, u32> {
        let mut stats = HashMap::new();
        
        for (_, labeled_data) in &self.labeled_data {
            let count = stats.entry(labeled_data.label.name.clone()).or_insert(0);
            *count += 1;
        }
        
        stats
    }
}