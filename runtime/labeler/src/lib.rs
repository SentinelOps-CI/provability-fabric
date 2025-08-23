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

use regex::Regex;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::fs;
use std::path::Path;

/// JSON path representation
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum JsonPath {
    Root,
    Field { parent: Box<JsonPath>, name: String },
    Index { parent: Box<JsonPath>, idx: usize },
}

impl JsonPath {
    /// Convert path to string representation
    pub fn to_string(&self) -> String {
        match self {
            JsonPath::Root => "$".to_string(),
            JsonPath::Field { parent, name } => {
                format!("{}.{}", parent.to_string(), name)
            }
            JsonPath::Index { parent, idx } => {
                format!("{}[{}]", parent.to_string(), idx)
            }
        }
    }

    /// Parse string representation to JsonPath
    pub fn from_string(s: &str) -> Result<Self, String> {
        if s == "$" {
            return Ok(JsonPath::Root);
        }

        // Simple parser for basic paths like $.field[0].subfield
        let mut parts = s.split('.');
        let mut current = JsonPath::Root;

        while let Some(part) = parts.next() {
            if part.is_empty() {
                continue;
            }

            // Handle array indices
            if part.contains('[') && part.contains(']') {
                let field_part = part.split('[').next().unwrap();
                let index_part = part.split('[').nth(1).unwrap().trim_end_matches(']');

                let idx = index_part
                    .parse::<usize>()
                    .map_err(|_| format!("Invalid index: {}", index_part))?;

                if !field_part.is_empty() {
                    current = JsonPath::Field {
                        parent: Box::new(current),
                        name: field_part.to_string(),
                    };
                }

                current = JsonPath::Index {
                    parent: Box::new(current),
                    idx,
                };
            } else {
                current = JsonPath::Field {
                    parent: Box::new(current),
                    name: part.to_string(),
                };
            }
        }

        Ok(current)
    }
}

/// Taint rule for labeling
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaintRule {
    pub path: String,
    pub label: String,
    pub condition: String,
    pub justification: Option<String>,
}

/// Labeler configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabelerConfig {
    pub rules: Vec<TaintRule>,
    pub default_label: String,
    pub unknown_fields_mode: bool,
    pub strict_mode: bool,
}

/// Labeler state during processing
#[derive(Debug, Clone)]
pub struct LabelerState {
    pub current_path: JsonPath,
    pub labels: HashMap<String, String>,
    pub witnesses: Vec<String>,
    pub processed_paths: HashMap<String, String>,
}

impl LabelerState {
    pub fn new() -> Self {
        Self {
            current_path: JsonPath::Root,
            labels: HashMap::new(),
            witnesses: Vec::new(),
            processed_paths: HashMap::new(),
        }
    }

    /// Add a label for a path
    pub fn add_label(&mut self, path: &JsonPath, label: &str) {
        let path_str = path.to_string();
        self.labels.insert(path_str.clone(), label.to_string());
        self.processed_paths.insert(path_str, label.to_string());
    }

    /// Get label for a path
    pub fn get_label(&self, path: &JsonPath) -> Option<&String> {
        let path_str = path.to_string();
        self.labels.get(&path_str)
    }
}

/// Labeler for JSON data with taint rules
pub struct Labeler {
    config: LabelerConfig,
    path_rules: HashMap<String, String>,
    json_patterns: Vec<Regex>,
}

impl Labeler {
    /// Create new labeler from configuration
    pub fn new(config: LabelerConfig) -> Self {
        let mut path_rules = HashMap::new();
        for rule in &config.rules {
            path_rules.insert(rule.path.clone(), rule.label.clone());
        }

        // Compile JSON-in-string patterns
        let json_patterns = vec![
            Regex::new(r"\{[^}]*\}").unwrap(),  // JSON object pattern
            Regex::new(r"\[[^\]]*\]").unwrap(), // JSON array pattern
        ];

        Self {
            config,
            path_rules,
            json_patterns,
        }
    }

    /// Load labeler from YAML file
    pub fn from_yaml_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let content = fs::read_to_string(path)?;
        let config: LabelerConfig = serde_yaml::from_str(&content)?;
        Ok(Self::new(config))
    }

    /// Label JSON value with taint rules
    pub fn label_json_value(
        &self,
        state: &mut LabelerState,
        value: &serde_json::Value,
    ) -> Result<String, String> {
        match value {
            serde_json::Value::Null => {
                let label = self.config.default_label.clone();
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
            serde_json::Value::Bool(_) => {
                let label = self.config.default_label.clone();
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
            serde_json::Value::Number(_) => {
                let label = self.config.default_label.clone();
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
            serde_json::Value::String(s) => {
                let label = self.label_string_value(s, state)?;
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
            serde_json::Value::Array(arr) => {
                let label = self.label_array_value(arr, state)?;
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
            serde_json::Value::Object(obj) => {
                let label = self.label_object_value(obj, state)?;
                state.add_label(&state.current_path, &label);
                Ok(label)
            }
        }
    }

    /// Label string value with special handling for JSON-in-string
    fn label_string_value(&self, s: &str, state: &mut LabelerState) -> Result<String, String> {
        // Check if string contains JSON-like patterns
        for pattern in &self.json_patterns {
            if pattern.is_match(s) {
                // JSON-in-string is treated as data, not instruction
                return Ok("data".to_string());
            }
        }

        // Check if current path matches any taint rules
        let path_str = state.current_path.to_string();
        if let Some(label) = self.path_rules.get(&path_str) {
            return Ok(label.clone());
        }

        // Default label for strings
        Ok(self.config.default_label.clone())
    }

    /// Label array value
    fn label_array_value(
        &self,
        arr: &[serde_json::Value],
        state: &mut LabelerState,
    ) -> Result<String, String> {
        for (idx, item) in arr.iter().enumerate() {
            let array_path = JsonPath::Index {
                parent: Box::new(state.current_path.clone()),
                idx,
            };
            let original_path = state.current_path.clone();
            state.current_path = array_path;

            self.label_json_value(state, item)?;

            state.current_path = original_path;
        }
        Ok("array".to_string())
    }

    /// Label object value
    fn label_object_value(
        &self,
        obj: &serde_json::Map<String, serde_json::Value>,
        state: &mut LabelerState,
    ) -> Result<String, String> {
        for (key, value) in obj {
            let field_path = JsonPath::Field {
                parent: Box::new(state.current_path.clone()),
                name: key.clone(),
            };
            let original_path = state.current_path.clone();
            state.current_path = field_path;

            self.label_json_value(state, value)?;

            state.current_path = original_path;
        }
        Ok("object".to_string())
    }

    /// Generate Merkle witness for labeled paths
    pub fn generate_merkle_witness(&self, state: &LabelerState) -> String {
        use sha2::{Digest, Sha256};

        let mut hasher = Sha256::new();

        // Sort paths for deterministic hashing
        let mut paths: Vec<_> = state.processed_paths.iter().collect();
        paths.sort_by_key(|(path, _)| path);

        for (path, label) in paths {
            hasher.update(path.as_bytes());
            hasher.update(label.as_bytes());
        }

        format!("{:x}", hasher.finalize())
    }

    /// Generate Bloom filter witness
    pub fn generate_bloom_witness(&self, state: &LabelerState) -> String {
        use sha2::{Digest, Sha256};

        let mut hasher = Sha256::new();

        // Create Bloom filter hash
        for (path, label) in &state.processed_paths {
            hasher.update(path.as_bytes());
            hasher.update(label.as_bytes());
        }

        format!("bloom_{:x}", hasher.finalize())
    }

    /// Validate labeler configuration
    pub fn validate_config(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        for rule in &self.config.rules {
            if rule.path.is_empty() {
                errors.push(format!("Rule has empty path"));
            }
            if rule.label.is_empty() {
                errors.push(format!("Rule for path '{}' has empty label", rule.path));
            }
            if rule.condition.is_empty() {
                errors.push(format!("Rule for path '{}' has empty condition", rule.path));
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Export labeler configuration to JSON
    pub fn export_config(&self) -> serde_json::Value {
        serde_json::json!({
            "rules": self.config.rules,
            "default_label": self.config.default_label,
            "unknown_fields_mode": self.config.unknown_fields_mode,
            "strict_mode": self.config.strict_mode
        })
    }
}

/// Generate labeler from schema and taint rules
pub fn generate_labeler(schema: &serde_json::Value, rules: &[TaintRule]) -> LabelerConfig {
    LabelerConfig {
        rules: rules.to_vec(),
        default_label: "untrusted".to_string(),
        unknown_fields_mode: true,
        strict_mode: true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn test_json_path_parsing() {
        let path = JsonPath::from_string("$.user.credentials.password").unwrap();
        assert_eq!(path.to_string(), "$.user.credentials.password");

        let array_path = JsonPath::from_string("$.users[0].name").unwrap();
        assert_eq!(array_path.to_string(), "$.users[0].name");
    }

    #[test]
    fn test_string_labeling() {
        let config = LabelerConfig {
            rules: vec![TaintRule {
                path: "$.password".to_string(),
                label: "secret".to_string(),
                condition: "always".to_string(),
                justification: None,
            }],
            default_label: "untrusted".to_string(),
            unknown_fields_mode: true,
            strict_mode: true,
        };

        let labeler = Labeler::new(config);
        let mut state = LabelerState::new();

        // Test JSON-in-string detection
        let json_string = json!("{\"key\": \"value\"}");
        let label = labeler
            .label_string_value("{\"key\": \"value\"}", &mut state)
            .unwrap();
        assert_eq!(label, "data");
    }

    #[test]
    fn test_object_labeling() {
        let config = LabelerConfig {
            rules: vec![TaintRule {
                path: "$.user.password".to_string(),
                label: "secret".to_string(),
                condition: "always".to_string(),
                justification: None,
            }],
            default_label: "untrusted".to_string(),
            unknown_fields_mode: true,
            strict_mode: true,
        };

        let labeler = Labeler::new(config);
        let mut state = LabelerState::new();

        let user_data = json!({
            "user": {
                "password": "secret123",
                "email": "user@example.com"
            }
        });

        labeler.label_json_value(&mut state, &user_data).unwrap();

        // Check that password path was labeled as secret
        let password_path = JsonPath::from_string("$.user.password").unwrap();
        assert_eq!(state.get_label(&password_path), Some(&"secret".to_string()));

        // Check that email path got default label
        let email_path = JsonPath::from_string("$.user.email").unwrap();
        assert_eq!(state.get_label(&email_path), Some(&"untrusted".to_string()));
    }

    #[test]
    fn test_witness_generation() {
        let config = LabelerConfig {
            rules: vec![],
            default_label: "untrusted".to_string(),
            unknown_fields_mode: true,
            strict_mode: true,
        };

        let labeler = Labeler::new(config);
        let mut state = LabelerState::new();

        let test_data = json!({
            "field1": "value1",
            "field2": "value2"
        });

        labeler.label_json_value(&mut state, &test_data).unwrap();

        let merkle_witness = labeler.generate_merkle_witness(&state);
        let bloom_witness = labeler.generate_bloom_witness(&state);

        assert!(!merkle_witness.is_empty());
        assert!(!bloom_witness.is_empty());
        assert!(bloom_witness.starts_with("bloom_"));
    }

    #[test]
    fn test_config_validation() {
        let valid_config = LabelerConfig {
            rules: vec![TaintRule {
                path: "$.test".to_string(),
                label: "test".to_string(),
                condition: "always".to_string(),
                justification: None,
            }],
            default_label: "untrusted".to_string(),
            unknown_fields_mode: true,
            strict_mode: true,
        };

        let labeler = Labeler::new(valid_config);
        assert!(labeler.validate_config().is_ok());

        let invalid_config = LabelerConfig {
            rules: vec![TaintRule {
                path: "".to_string(),
                label: "test".to_string(),
                condition: "always".to_string(),
                justification: None,
            }],
            default_label: "untrusted".to_string(),
            unknown_fields_mode: true,
            strict_mode: true,
        };

        let invalid_labeler = Labeler::new(invalid_config);
        assert!(invalid_labeler.validate_config().is_err());
    }
}
