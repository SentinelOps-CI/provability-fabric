/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE/2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::hash::{Hash, Hasher};

/// Security label type
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecurityLabel {
    Public,
    Confidential,
    Secret,
    Custom(String),
}

impl SecurityLabel {
    /// Convert to string representation
    pub fn to_string(&self) -> String {
        match self {
            SecurityLabel::Public => "public".to_string(),
            SecurityLabel::Confidential => "confidential".to_string(),
            SecurityLabel::Secret => "secret".to_string(),
            SecurityLabel::Custom(name) => format!("custom:{}", name),
        }
    }

    /// Parse from string representation
    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "public" => Ok(SecurityLabel::Public),
            "confidential" => Ok(SecurityLabel::Confidential),
            "secret" => Ok(SecurityLabel::Secret),
            s if s.starts_with("custom:") => {
                let name = s.strip_prefix("custom:").unwrap();
                Ok(SecurityLabel::Custom(name.to_string()))
            }
            _ => Err(format!("Unknown security label: {}", s)),
        }
    }

    /// Check if this label is less than or equal to another (lattice ordering)
    pub fn le(&self, other: &SecurityLabel) -> bool {
        match (self, other) {
            (SecurityLabel::Public, _) => true,
            (SecurityLabel::Confidential, SecurityLabel::Confidential) => true,
            (SecurityLabel::Confidential, SecurityLabel::Secret) => true,
            (SecurityLabel::Secret, SecurityLabel::Secret) => true,
            (SecurityLabel::Custom(name1), SecurityLabel::Custom(name2)) => name1 == name2,
            _ => false,
        }
    }

    /// Check if this label is greater than or equal to another
    pub fn ge(&self, other: &SecurityLabel) -> bool {
        other.le(self)
    }

    /// Check if this label is strictly less than another
    pub fn lt(&self, other: &SecurityLabel) -> bool {
        self.le(other) && self != other
    }

    /// Check if this label is strictly greater than another
    pub fn gt(&self, other: &SecurityLabel) -> bool {
        other.lt(self)
    }
}

/// Declassification rule
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclassRule {
    pub from_label: SecurityLabel,
    pub to_label: SecurityLabel,
    pub conditions: Vec<String>,
    pub derivation: String,
}

/// Declassification block Δ
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeclassBlock {
    pub rules: Vec<DeclassRule>,
}

impl DeclassBlock {
    /// Create new declassification block
    pub fn new(rules: Vec<DeclassRule>) -> Self {
        Self { rules }
    }

    /// Check if declassification block is well-formed
    pub fn is_well_formed(&self) -> Result<bool, String> {
        // Check for cycles
        if self.has_cycles()? {
            return Ok(false);
        }

        // Check that all declassifications narrow labels
        for rule in &self.rules {
            if !rule.to_label.le(&rule.from_label) {
                return Err(format!(
                    "Declassification rule widens labels: {} -> {}",
                    rule.from_label.to_string(),
                    rule.to_label.to_string()
                ));
            }
        }

        // Check that conditions are non-empty
        for rule in &self.rules {
            if rule.conditions.is_empty() {
                return Err(format!(
                    "Declassification rule has no conditions: {} -> {}",
                    rule.from_label.to_string(),
                    rule.to_label.to_string()
                ));
            }
        }

        // Check that derivation is specified
        for rule in &self.rules {
            if rule.derivation.is_empty() {
                return Err(format!(
                    "Declassification rule has no derivation: {} -> {}",
                    rule.from_label.to_string(),
                    rule.to_label.to_string()
                ));
            }
        }

        Ok(true)
    }

    /// Check for cycles in declassification rules
    fn has_cycles(&self) -> Result<bool, String> {
        // Build adjacency list for declassification graph
        let mut graph: HashMap<SecurityLabel, Vec<SecurityLabel>> = HashMap::new();

        for rule in &self.rules {
            graph
                .entry(rule.from_label.clone())
                .or_insert_with(Vec::new)
                .push(rule.to_label.clone());
        }

        // Check for cycles using DFS
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();

        for node in graph.keys() {
            if !visited.contains(node) {
                if self.is_cyclic_util(node, &graph, &mut visited, &mut rec_stack)? {
                    return Ok(true);
                }
            }
        }

        Ok(false)
    }

    /// DFS utility for cycle detection
    fn is_cyclic_util(
        &self,
        node: &SecurityLabel,
        graph: &HashMap<SecurityLabel, Vec<SecurityLabel>>,
        visited: &mut HashSet<SecurityLabel>,
        rec_stack: &mut HashSet<SecurityLabel>,
    ) -> Result<bool, String> {
        visited.insert(node.clone());
        rec_stack.insert(node.clone());

        if let Some(neighbors) = graph.get(node) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    if self.is_cyclic_util(neighbor, graph, visited, rec_stack)? {
                        return Ok(true);
                    }
                } else if rec_stack.contains(neighbor) {
                    return Ok(true);
                }
            }
        }

        rec_stack.remove(node);
        Ok(false)
    }

    /// Check if declassification is allowed
    pub fn declass_allowed(&self, from_label: &SecurityLabel, to_label: &SecurityLabel) -> bool {
        self.rules
            .iter()
            .any(|rule| rule.from_label == *from_label && rule.to_label == *to_label)
    }

    /// Verify declassification with conditions
    pub fn verify_declass(
        &self,
        from_label: &SecurityLabel,
        to_label: &SecurityLabel,
        conditions: &[String],
    ) -> Result<bool, String> {
        // Check if declassification is allowed
        if !self.declass_allowed(from_label, to_label) {
            return Ok(false);
        }

        // Find matching rule
        let rule = self
            .rules
            .iter()
            .find(|rule| rule.from_label == *from_label && rule.to_label == *to_label)
            .ok_or("No matching declassification rule found")?;

        // Check conditions
        if rule.conditions != conditions {
            return Err(format!(
                "Conditions mismatch: expected {:?}, got {:?}",
                rule.conditions, conditions
            ));
        }

        Ok(true)
    }

    /// Get all declassification rules
    pub fn rules(&self) -> &[DeclassRule] {
        &self.rules
    }

    /// Add a declassification rule
    pub fn add_rule(&mut self, rule: DeclassRule) -> Result<(), String> {
        // Check if rule would create cycles
        let mut temp_rules = self.rules.clone();
        temp_rules.push(rule.clone());
        let temp_block = DeclassBlock::new(temp_rules);

        if temp_block.has_cycles()? {
            return Err("Adding this rule would create cycles".to_string());
        }

        // Check if rule widens labels
        if !rule.to_label.le(&rule.from_label) {
            return Err("Declassification rule cannot widen labels".to_string());
        }

        self.rules.push(rule);
        Ok(())
    }

    /// Remove a declassification rule
    pub fn remove_rule(&mut self, index: usize) -> Result<DeclassRule, String> {
        if index >= self.rules.len() {
            return Err("Rule index out of bounds".to_string());
        }
        Ok(self.rules.remove(index))
    }
}

/// Declassification enforcer
pub struct DeclassEnforcer {
    declass_block: DeclassBlock,
    strict_mode: bool,
}

impl DeclassEnforcer {
    /// Create new declassification enforcer
    pub fn new(declass_block: DeclassBlock) -> Result<Self, String> {
        // Verify that the declassification block is well-formed
        if !declass_block.is_well_formed()? {
            return Err("Declassification block is not well-formed".to_string());
        }

        Ok(Self {
            declass_block,
            strict_mode: true,
        })
    }

    /// Enforce declassification
    pub fn enforce_declass(
        &self,
        from_label: &SecurityLabel,
        to_label: &SecurityLabel,
        conditions: &[String],
    ) -> Result<bool, String> {
        // In strict mode, reject any declassification without a matching rule
        if self.strict_mode && !self.declass_block.declass_allowed(from_label, to_label) {
            return Err(format!(
                "Declassification not allowed: {} -> {}",
                from_label.to_string(),
                to_label.to_string()
            ));
        }

        // Verify the declassification
        self.declass_block
            .verify_declass(from_label, to_label, conditions)
    }

    /// Check if declassification widens labels (should be denied)
    pub fn check_label_widening(
        &self,
        from_label: &SecurityLabel,
        to_label: &SecurityLabel,
    ) -> bool {
        // If to_label is greater than from_label, it's widening
        to_label.gt(from_label)
    }

    /// Set strict mode
    pub fn set_strict_mode(&mut self, strict: bool) {
        self.strict_mode = strict;
    }

    /// Check if strict mode is enabled
    pub fn is_strict_mode(&self) -> bool {
        self.strict_mode
    }

    /// Get the declassification block
    pub fn declass_block(&self) -> &DeclassBlock {
        &self.declass_block
    }

    /// Update declassification block
    pub fn update_declass_block(&mut self, new_block: DeclassBlock) -> Result<(), String> {
        // Verify the new block is well-formed
        if !new_block.is_well_formed()? {
            return Err("New declassification block is not well-formed".to_string());
        }

        self.declass_block = new_block;
        Ok(())
    }
}

/// Load declassification block from file
pub fn load_declass_block<P: AsRef<std::path::Path>>(
    path: P,
) -> Result<DeclassBlock, Box<dyn Error>> {
    let content = std::fs::read_to_string(path)?;
    let block: DeclassBlock = serde_json::from_str(&content)?;
    Ok(block)
}

/// Save declassification block to file
pub fn save_declass_block<P: AsRef<std::path::Path>>(
    block: &DeclassBlock,
    path: P,
) -> Result<(), Box<dyn Error>> {
    let content = serde_json::to_string_pretty(block)?;
    std::fs::write(path, content)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_security_label_ordering() {
        assert!(SecurityLabel::Public.le(&SecurityLabel::Confidential));
        assert!(SecurityLabel::Public.le(&SecurityLabel::Secret));
        assert!(SecurityLabel::Confidential.le(&SecurityLabel::Secret));
        assert!(!SecurityLabel::Secret.le(&SecurityLabel::Public));
        assert!(!SecurityLabel::Confidential.le(&SecurityLabel::Public));
    }

    #[test]
    fn test_declass_rule_creation() {
        let rule = DeclassRule {
            from_label: SecurityLabel::Secret,
            to_label: SecurityLabel::Confidential,
            conditions: vec!["aggregated".to_string()],
            derivation: "data_aggregation".to_string(),
        };

        assert_eq!(rule.from_label, SecurityLabel::Secret);
        assert_eq!(rule.to_label, SecurityLabel::Confidential);
        assert_eq!(rule.conditions, vec!["aggregated"]);
        assert_eq!(rule.derivation, "data_aggregation");
    }

    #[test]
    fn test_well_formed_declass_block() {
        let rules = vec![
            DeclassRule {
                from_label: SecurityLabel::Secret,
                to_label: SecurityLabel::Confidential,
                conditions: vec!["aggregated".to_string()],
                derivation: "data_aggregation".to_string(),
            },
            DeclassRule {
                from_label: SecurityLabel::Confidential,
                to_label: SecurityLabel::Public,
                conditions: vec!["anonymized".to_string()],
                derivation: "anonymization".to_string(),
            },
        ];

        let block = DeclassBlock::new(rules);
        assert!(block.is_well_formed().unwrap());
    }

    #[test]
    fn test_ill_formed_declass_block() {
        let rules = vec![DeclassRule {
            from_label: SecurityLabel::Public,
            to_label: SecurityLabel::Secret, // Widens labels
            conditions: vec!["condition".to_string()],
            derivation: "derivation".to_string(),
        }];

        let block = DeclassBlock::new(rules);
        assert!(!block.is_well_formed().unwrap());
    }

    #[test]
    fn test_declass_enforcement() {
        let rules = vec![DeclassRule {
            from_label: SecurityLabel::Secret,
            to_label: SecurityLabel::Confidential,
            conditions: vec!["aggregated".to_string()],
            derivation: "data_aggregation".to_string(),
        }];

        let block = DeclassBlock::new(rules);
        let enforcer = DeclassEnforcer::new(block).unwrap();

        let result = enforcer.enforce_declass(
            &SecurityLabel::Secret,
            &SecurityLabel::Confidential,
            &["aggregated".to_string()],
        );

        assert!(result.unwrap());
    }

    #[test]
    fn test_label_widening_detection() {
        let rules = vec![DeclassRule {
            from_label: SecurityLabel::Public,
            to_label: SecurityLabel::Secret,
            conditions: vec!["condition".to_string()],
            derivation: "derivation".to_string(),
        }];

        let block = DeclassBlock::new(rules);
        let enforcer = DeclassEnforcer::new(block).unwrap();

        assert!(enforcer.check_label_widening(&SecurityLabel::Public, &SecurityLabel::Secret));
    }
}
