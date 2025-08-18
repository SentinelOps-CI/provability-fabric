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
use std::collections::HashMap;
use std::error::Error;
use std::hash::{Hash, Hasher};

/// Event types as defined in the labeled alphabet
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EventType {
    Call,
    Log,
    Declassify,
    Emit,
    Retrieve,
    DataQuery,
    Search,
    Fetch,
    Get,
    Compute,
    Analyze,
    Transform,
    Aggregate,
    Notify,
    Alert,
    Report,
    Export,
    Validate,
    Verify,
    Audit,
    ComplianceCheck,
}

impl EventType {
    /// Convert to string representation
    pub fn to_string(&self) -> &'static str {
        match self {
            EventType::Call => "call",
            EventType::Log => "log",
            EventType::Declassify => "declassify",
            EventType::Emit => "emit",
            EventType::Retrieve => "retrieve",
            EventType::DataQuery => "data_query",
            EventType::Search => "search",
            EventType::Fetch => "fetch",
            EventType::Get => "get",
            EventType::Compute => "compute",
            EventType::Analyze => "analyze",
            EventType::Transform => "transform",
            EventType::Aggregate => "aggregate",
            EventType::Notify => "notify",
            EventType::Alert => "alert",
            EventType::Report => "report",
            EventType::Export => "export",
            EventType::Validate => "validate",
            EventType::Verify => "verify",
            EventType::Audit => "audit",
            EventType::ComplianceCheck => "compliance_check",
        }
    }

    /// Parse from string representation
    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "call" => Ok(EventType::Call),
            "log" => Ok(EventType::Log),
            "declassify" => Ok(EventType::Declassify),
            "emit" => Ok(EventType::Emit),
            "retrieve" => Ok(EventType::Retrieve),
            "data_query" => Ok(EventType::DataQuery),
            "search" => Ok(EventType::Search),
            "fetch" => Ok(EventType::Fetch),
            "get" => Ok(EventType::Get),
            "compute" => Ok(EventType::Compute),
            "analyze" => Ok(EventType::Analyze),
            "transform" => Ok(EventType::Transform),
            "aggregate" => Ok(EventType::Aggregate),
            "notify" => Ok(EventType::Notify),
            "alert" => Ok(EventType::Alert),
            "report" => Ok(EventType::Report),
            "export" => Ok(EventType::Export),
            "validate" => Ok(EventType::Validate),
            "verify" => Ok(EventType::Verify),
            "audit" => Ok(EventType::Audit),
            "compliance_check" => Ok(EventType::ComplianceCheck),
            _ => Err(format!("Unknown event type: {}", s)),
        }
    }
}

/// Field commitment for integrity verification
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FieldCommitment {
    pub field_name: String,
    pub hash: String,
    pub salt: String,
}

/// Operation arguments with integrity hashing
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct OperationArgs {
    pub field_commit: String, // SHA-256 hash of field commitments
    pub args_hash: String,    // SHA-256 hash of operation arguments
    pub raw_args: HashMap<String, serde_json::Value>,
}

impl OperationArgs {
    /// Create new operation args with automatic hashing
    pub fn new(raw_args: HashMap<String, serde_json::Value>) -> Result<Self, String> {
        let field_commit = Self::compute_field_commit(&raw_args)?;
        let args_hash = Self::compute_args_hash(&raw_args)?;

        Ok(Self {
            field_commit,
            args_hash,
            raw_args,
        })
    }

    /// Compute field commitment hash
    fn compute_field_commit(args: &HashMap<String, serde_json::Value>) -> Result<String, String> {
        let mut hasher = DefaultHasher::new();

        // Sort fields for deterministic hashing
        let mut fields: Vec<_> = args.keys().collect();
        fields.sort();

        for field in fields {
            field.hash(&mut hasher);
            if let Some(value) = args.get(field) {
                // Hash the value type and content
                std::any::TypeId::of::<serde_json::Value>().hash(&mut hasher);
                value.to_string().hash(&mut hasher);
            }
        }

        Ok(format!("{:x}", hasher.finish()))
    }

    /// Compute arguments hash
    fn compute_args_hash(args: &HashMap<String, serde_json::Value>) -> Result<String, String> {
        let mut hasher = DefaultHasher::new();

        // Sort for deterministic hashing
        let mut entries: Vec<_> = args.iter().collect();
        entries.sort_by(|a, b| a.0.cmp(b.0));

        for (key, value) in entries {
            key.hash(&mut hasher);
            value.to_string().hash(&mut hasher);
        }

        Ok(format!("{:x}", hasher.finish()))
    }

    /// Verify field commitment
    pub fn verify_field_commit(&self) -> Result<bool, String> {
        let computed = Self::compute_field_commit(&self.raw_args)?;
        Ok(computed == self.field_commit)
    }

    /// Verify arguments hash
    pub fn verify_args_hash(&self) -> Result<bool, String> {
        let computed = Self::compute_args_hash(&self.raw_args)?;
        Ok(computed == self.args_hash)
    }

    /// Get raw argument value
    pub fn get_arg(&self, key: &str) -> Option<&serde_json::Value> {
        self.raw_args.get(key)
    }

    /// Get all raw arguments
    pub fn get_all_args(&self) -> &HashMap<String, serde_json::Value> {
        &self.raw_args
    }
}

/// Typed event with mediation support
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypedEvent {
    pub event_type: EventType,
    pub args: OperationArgs,
    pub labels_in: Vec<String>,
    pub labels_out: Vec<String>,
    pub caps_required: Vec<String>,
    pub timestamp: u64,
    pub session_id: String,
    pub plan_hash: String,
}

impl TypedEvent {
    /// Create new typed event
    pub fn new(
        event_type: EventType,
        raw_args: HashMap<String, serde_json::Value>,
        labels_in: Vec<String>,
        labels_out: Vec<String>,
        caps_required: Vec<String>,
        session_id: String,
        plan_hash: String,
    ) -> Result<Self, String> {
        let args = OperationArgs::new(raw_args)?;
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| format!("Time error: {}", e))?
            .as_secs();

        Ok(Self {
            event_type,
            args,
            labels_in,
            labels_out,
            caps_required,
            timestamp,
            session_id,
            plan_hash,
        })
    }

    /// Verify event integrity
    pub fn verify_integrity(&self) -> Result<bool, String> {
        let field_commit_ok = self.args.verify_field_commit()?;
        let args_hash_ok = self.args.verify_args_hash()?;

        Ok(field_commit_ok && args_hash_ok)
    }

    /// Check if event requires specific capability
    pub fn requires_capability(&self, cap: &str) -> bool {
        self.caps_required.contains(&cap.to_string())
    }

    /// Check if event has input label
    pub fn has_input_label(&self, label: &str) -> bool {
        self.labels_in.contains(&label.to_string())
    }

    /// Check if event produces output label
    pub fn produces_output_label(&self, label: &str) -> bool {
        self.labels_out.contains(&label.to_string())
    }

    /// Get event type as string
    pub fn event_type_str(&self) -> &'static str {
        self.event_type.to_string()
    }

    /// Get field commitment
    pub fn field_commit(&self) -> &str {
        &self.args.field_commit
    }

    /// Get arguments hash
    pub fn args_hash(&self) -> &str {
        &self.args.args_hash
    }
}

/// Event mediator for runtime enforcement
pub struct EventMediator {
    allowed_operations: Vec<EventType>,
    plan_nodes: HashMap<String, PlanNode>,
    strict_mode: bool,
}

/// Plan node for authorization
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PlanNode {
    pub operation: EventType,
    pub field_commit: String,
    pub args_hash: String,
    pub caps_required: Vec<String>,
    pub labels_in: Vec<String>,
    pub labels_out: Vec<String>,
}

impl EventMediator {
    /// Create new event mediator
    pub fn new(allowed_operations: Vec<EventType>, strict_mode: bool) -> Self {
        Self {
            allowed_operations,
            plan_nodes: HashMap::new(),
            strict_mode,
        }
    }

    /// Add plan node for authorization
    pub fn add_plan_node(&mut self, node_id: String, node: PlanNode) {
        self.plan_nodes.insert(node_id, node);
    }

    /// Mediate event execution
    pub fn mediate_event(&self, event: &TypedEvent) -> Result<bool, String> {
        // Check if operation is allowed
        if !self.allowed_operations.contains(&event.event_type) {
            return Err(format!(
                "Operation {} not in allowed operations",
                event.event_type_str()
            ));
        }

        // Verify event integrity
        if !event.verify_integrity()? {
            return Err("Event integrity check failed".to_string());
        }

        // Check if event matches a plan node
        let plan_node = self.find_matching_plan_node(event)?;

        // Verify field commitment
        if event.field_commit() != plan_node.field_commit {
            return Err("Field commitment mismatch".to_string());
        }

        // Verify arguments hash
        if event.args_hash() != plan_node.args_hash {
            return Err("Arguments hash mismatch".to_string());
        }

        // Verify capabilities
        for cap in &event.caps_required {
            if !plan_node.caps_required.contains(cap) {
                return Err(format!("Required capability {} not in plan node", cap));
            }
        }

        // Verify label flow
        for label in &event.labels_in {
            if !plan_node.labels_in.contains(label) {
                return Err(format!("Input label {} not in plan node", label));
            }
        }

        for label in &event.labels_out {
            if !plan_node.labels_out.contains(label) {
                return Err(format!("Output label {} not in plan node", label));
            }
        }

        Ok(true)
    }

    /// Find matching plan node
    fn find_matching_plan_node(&self, event: &TypedEvent) -> Result<&PlanNode, String> {
        for (_, node) in &self.plan_nodes {
            if node.operation == event.event_type {
                return Ok(node);
            }
        }

        Err(format!(
            "No plan node found for operation {}",
            event.event_type_str()
        ))
    }

    /// Set strict mode
    pub fn set_strict_mode(&mut self, strict: bool) {
        self.strict_mode = strict;
    }

    /// Check if strict mode is enabled
    pub fn is_strict_mode(&self) -> bool {
        self.strict_mode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_event_type_parsing() {
        assert_eq!(EventType::Call.to_string(), "call");
        assert_eq!(EventType::from_string("call").unwrap(), EventType::Call);
        assert!(EventType::from_string("unknown").is_err());
    }

    #[test]
    fn test_operation_args_hashing() {
        let mut args = HashMap::new();
        args.insert("key1".to_string(), serde_json::json!("value1"));
        args.insert("key2".to_string(), serde_json::json!(42));

        let op_args = OperationArgs::new(args).unwrap();
        assert!(op_args.verify_field_commit().unwrap());
        assert!(op_args.verify_args_hash().unwrap());
    }

    #[test]
    fn test_typed_event_creation() {
        let mut args = HashMap::new();
        args.insert("param".to_string(), serde_json::json!("value"));

        let event = TypedEvent::new(
            EventType::Call,
            args,
            vec!["input_label".to_string()],
            vec!["output_label".to_string()],
            vec!["capability".to_string()],
            "session123".to_string(),
            "plan_hash".to_string(),
        )
        .unwrap();

        assert_eq!(event.event_type, EventType::Call);
        assert!(event.verify_integrity().unwrap());
    }

    #[test]
    fn test_event_mediation() {
        let mut mediator = EventMediator::new(vec![EventType::Call], true);

        let plan_node = PlanNode {
            operation: EventType::Call,
            field_commit: "hash123".to_string(),
            args_hash: "args456".to_string(),
            caps_required: vec!["cap1".to_string()],
            labels_in: vec!["input".to_string()],
            labels_out: vec!["output".to_string()],
        };

        mediator.add_plan_node("node1".to_string(), plan_node);

        let mut args = HashMap::new();
        args.insert("param".to_string(), serde_json::json!("value"));

        let event = TypedEvent::new(
            EventType::Call,
            args,
            vec!["input".to_string()],
            vec!["output".to_string()],
            vec!["cap1".to_string()],
            "session123".to_string(),
            "plan_hash".to_string(),
        )
        .unwrap();

        // This will fail because the hashes don't match the plan node
        assert!(mediator.mediate_event(&event).is_err());
    }
}
