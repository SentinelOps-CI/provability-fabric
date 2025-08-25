// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use tempfile::tempdir;

// Import the enhanced adapters and policy adapter
use runtime::sidecar_watcher::policy_adapter::{
    Action, Ctx, DocId, DocMeta, DocumentState, EnforcementMode, Label, PolicyAdapter,
    PolicyConfig, Principal, Tool, WorldState,
};

// Mock HTTP-GET adapter for testing
#[derive(Debug, Clone)]
struct MockHttpGetAdapter {
    resource_mapping: Option<MockHttpGetResource>,
    witness_required: bool,
    high_assurance_mode: bool,
}

#[derive(Debug, Clone)]
struct MockHttpGetResource {
    doc_id: String,
    field_path: Vec<String>,
    merkle_root: String,
    field_commit: String,
    label: String,
}

#[derive(Debug, Clone)]
struct MockHttpGetWitness {
    merkle_path: Vec<String>,
    field_commit: String,
    timestamp: u64,
    signature: String,
}

impl MockHttpGetAdapter {
    fn new(
        resource_mapping: Option<MockHttpGetResource>,
        witness_required: bool,
        high_assurance_mode: bool,
    ) -> Self {
        Self {
            resource_mapping,
            witness_required,
            high_assurance_mode,
        }
    }

    fn execute(
        &self,
        url: &str,
        witness: Option<&MockHttpGetWitness>,
    ) -> Result<MockHttpGetResponse, Box<dyn std::error::Error>> {
        // Simulate HTTP request
        let response_body = r#"{"users": [{"id": 1, "name": "Alice"}, {"id": 2, "name": "Bob"}]}"#;

        // Validate witness if required
        let witness_valid = if self.witness_required {
            if let Some(w) = witness {
                w.field_commit == "valid_commit_hash" && w.timestamp > 0
            } else {
                false
            }
        } else {
            true
        };

        if !witness_valid {
            return Err("Witness validation failed".into());
        }

        // Validate resource access if resource mapping is provided
        let resource_access_ok = if let Some(ref resource) = self.resource_mapping {
            if self.high_assurance_mode {
                witness.is_some() && witness.as_ref().unwrap().field_commit == resource.field_commit
            } else {
                true
            }
        } else {
            true
        };

        if !resource_access_ok {
            return Err("Resource access validation failed".into());
        }

        Ok(MockHttpGetResponse {
            status_code: 200,
            body: response_body.as_bytes().to_vec(),
            witness_validation: WitnessValidationResult {
                valid: witness_valid,
                merkle_path_verified: true,
                field_commit_verified: true,
                timestamp_valid: true,
                signature_valid: true,
                error_message: None,
            },
            resource_access: ResourceAccessResult {
                access_granted: resource_access_ok,
                label_derivation_ok: true,
                declass_rule_applied: None,
                flow_violation: None,
                permitted_fields: vec!["id".to_string(), "name".to_string()],
            },
        })
    }
}

#[derive(Debug, Clone)]
struct MockHttpGetResponse {
    status_code: u16,
    body: Vec<u8>,
    witness_validation: WitnessValidationResult,
    resource_access: ResourceAccessResult,
}

#[derive(Debug, Clone)]
struct WitnessValidationResult {
    valid: bool,
    merkle_path_verified: bool,
    field_commit_verified: bool,
    timestamp_valid: bool,
    signature_valid: bool,
    error_message: Option<String>,
}

#[derive(Debug, Clone)]
struct ResourceAccessResult {
    access_granted: bool,
    label_derivation_ok: bool,
    declass_rule_applied: Option<String>,
    flow_violation: Option<String>,
    permitted_fields: Vec<String>,
}

// Mock File-read adapter for testing
#[derive(Debug, Clone)]
struct MockFileReadAdapter {
    resource_mapping: Option<MockFileReadResource>,
    witness_required: bool,
    high_assurance_mode: bool,
}

#[derive(Debug, Clone)]
struct MockFileReadResource {
    doc_id: String,
    field_path: Vec<String>,
    merkle_root: String,
    field_commit: String,
    label: String,
    content_type: String,
}

#[derive(Debug, Clone)]
struct MockFileReadWitness {
    merkle_path: Vec<String>,
    field_commit: String,
    timestamp: u64,
    signature: String,
    file_hash: String,
}

impl MockFileReadAdapter {
    fn new(
        resource_mapping: Option<MockFileReadResource>,
        witness_required: bool,
        high_assurance_mode: bool,
    ) -> Self {
        Self {
            resource_mapping,
            witness_required,
            high_assurance_mode,
        }
    }

    fn execute(
        &self,
        file_path: &str,
        witness: Option<&MockFileReadWitness>,
    ) -> Result<MockFileReadResponse, Box<dyn std::error::Error>> {
        // Simulate file read
        let file_content = r#"{"users": [{"id": 1, "name": "Alice"}, {"id": 2, "name": "Bob"}]}"#;

        // Validate witness if required
        let witness_valid = if self.witness_required {
            if let Some(w) = witness {
                w.field_commit == "valid_commit_hash" && w.timestamp > 0
            } else {
                false
            }
        } else {
            true
        };

        if !witness_valid {
            return Err("Witness validation failed".into());
        }

        // Validate resource access if resource mapping is provided
        let resource_access_ok = if let Some(ref resource) = self.resource_mapping {
            if self.high_assurance_mode {
                witness.is_some() && witness.as_ref().unwrap().field_commit == resource.field_commit
            } else {
                true
            }
        } else {
            true
        };

        if !resource_access_ok {
            return Err("Resource access validation failed".into());
        }

        Ok(MockFileReadResponse {
            content: file_content.as_bytes().to_vec(),
            file_size: file_content.len() as u64,
            witness_validation: WitnessValidationResult {
                valid: witness_valid,
                merkle_path_verified: true,
                field_commit_verified: true,
                timestamp_valid: true,
                signature_valid: true,
                file_hash_verified: true,
                error_message: None,
            },
            resource_access: ResourceAccessResult {
                access_granted: resource_access_ok,
                label_derivation_ok: true,
                declass_rule_applied: None,
                flow_violation: None,
                permitted_fields: vec!["id".to_string(), "name".to_string()],
            },
        })
    }
}

#[derive(Debug, Clone)]
struct MockFileReadResponse {
    content: Vec<u8>,
    file_size: u64,
    witness_validation: WitnessValidationResult,
    resource_access: ResourceAccessResult,
}

// Integration test structure
struct AdapterIntegrationTest {
    policy_adapter: PolicyAdapter,
    http_adapter: MockHttpGetAdapter,
    file_adapter: MockFileReadAdapter,
    world_state: WorldState,
}

impl AdapterIntegrationTest {
    fn new() -> Self {
        let config = PolicyConfig {
            enforcement_mode: EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: true,
        };

        let policy_adapter = PolicyAdapter::new(config);

        // Create HTTP adapter with resource mapping
        let http_resource = MockHttpGetResource {
            doc_id: "https://api.example.com/users".to_string(),
            field_path: vec!["users".to_string()],
            merkle_root: "merkle_root_123".to_string(),
            field_commit: "valid_commit_hash".to_string(),
            label: "internal".to_string(),
        };

        let http_adapter = MockHttpGetAdapter::new(
            Some(http_resource),
            true, // witness_required
            true, // high_assurance_mode
        );

        // Create file adapter with resource mapping
        let file_resource = MockFileReadResource {
            doc_id: "/tmp/users.json".to_string(),
            field_path: vec!["users".to_string()],
            merkle_root: "merkle_root_456".to_string(),
            field_commit: "valid_commit_hash".to_string(),
            label: "internal".to_string(),
            content_type: "json".to_string(),
        };

        let file_adapter = MockFileReadAdapter::new(
            Some(file_resource),
            true, // witness_required
            true, // high_assurance_mode
        );

        // Create world state
        let mut world_state = WorldState::new(1);

        // Add document states
        let doc_state = DocumentState::new("owner1".to_string(), "merkle_root_123".to_string());
        world_state.add_document(
            &DocId {
                uri: "https://api.example.com/users".to_string(),
                version: 1,
            },
            doc_state,
        );

        let doc_state2 = DocumentState::new("owner2".to_string(), "merkle_root_456".to_string());
        world_state.add_document(
            &DocId {
                uri: "/tmp/users.json".to_string(),
                version: 1,
            },
            doc_state2,
        );

        Self {
            policy_adapter,
            http_adapter,
            file_adapter,
            world_state,
        }
    }

    fn test_http_get_with_witness(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing HTTP-GET with valid witness...");

        let witness = MockHttpGetWitness {
            merkle_path: vec!["root".to_string(), "users".to_string()],
            field_commit: "valid_commit_hash".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            signature: "valid_signature".to_string(),
        };

        let response = self
            .http_adapter
            .execute("https://api.example.com/users", Some(&witness))?;

        assert!(response.witness_validation.valid);
        assert!(response.resource_access.access_granted);
        assert_eq!(response.status_code, 200);
        assert!(!response.body.is_empty());

        println!("✅ HTTP-GET with valid witness succeeded");
        Ok(())
    }

    fn test_http_get_without_witness(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing HTTP-GET without witness (should fail)...");

        let result = self
            .http_adapter
            .execute("https://api.example.com/users", None);

        assert!(result.is_err());
        let error_msg = result.unwrap_err().to_string();
        assert!(error_msg.contains("Witness validation failed"));

        println!("✅ HTTP-GET without witness properly rejected");
        Ok(())
    }

    fn test_file_read_with_witness(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing file read with valid witness...");

        let witness = MockFileReadWitness {
            merkle_path: vec!["root".to_string(), "users".to_string()],
            field_commit: "valid_commit_hash".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
            signature: "valid_signature".to_string(),
            file_hash: "file_hash_123".to_string(),
        };

        let response = self
            .file_adapter
            .execute("/tmp/users.json", Some(&witness))?;

        assert!(response.witness_validation.valid);
        assert!(response.resource_access.access_granted);
        assert_eq!(response.file_size, 65); // Length of test JSON
        assert!(!response.content.is_empty());

        println!("✅ File read with valid witness succeeded");
        Ok(())
    }

    fn test_file_read_without_witness(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing file read without witness (should fail)...");

        let result = self.file_adapter.execute("/tmp/users.json", None);

        assert!(result.is_err());
        let error_msg = result.unwrap_err().to_string();
        assert!(error_msg.contains("Witness validation failed"));

        println!("✅ File read without witness properly rejected");
        Ok(())
    }

    fn test_policy_adapter_integration(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing policy adapter integration...");

        let principal = Principal {
            id: "test-user".to_string(),
            roles: vec!["reader".to_string()],
            org: "test-org".to_string(),
        };

        let context = Ctx {
            session: "session-1".to_string(),
            epoch: 1,
            attributes: vec![("project".to_string(), "test-project".to_string())],
            tenant: "test-tenant".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
        };

        // Test read permission
        let read_action = Action::Read {
            doc: DocId {
                uri: "https://api.example.com/users".to_string(),
                version: 1,
            },
            path: vec!["users".to_string()],
        };

        let result = self.policy_adapter.evaluate_permission(
            &principal,
            &read_action,
            &context,
            Some(&self.world_state),
        )?;

        assert!(result.allowed);
        assert_eq!(result.permit_decision, "accept");
        assert!(result.path_witness_ok);
        assert!(result.label_derivation_ok);

        println!("✅ Policy adapter integration succeeded");
        Ok(())
    }

    fn test_epoch_validation(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("Testing epoch validation...");

        let principal = Principal {
            id: "test-user".to_string(),
            roles: vec!["admin".to_string()],
            org: "test-org".to_string(),
        };

        let context = Ctx {
            session: "session-1".to_string(),
            epoch: 0, // Old epoch
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)?
                .as_secs(),
        };

        let action = Action::Call {
            tool: Tool::SendEmail,
        };

        let result = self.policy_adapter.evaluate_permission(
            &principal,
            &action,
            &context,
            Some(&self.world_state),
        )?;

        assert!(!result.allowed);
        assert_eq!(result.permit_decision, "reject");
        assert!(result.reason.contains("Epoch validation failed"));

        println!("✅ Epoch validation succeeded");
        Ok(())
    }

    fn run_all_tests(&self) -> Result<(), Box<dyn std::error::Error>> {
        println!("🚀 Running adapter integration tests...\n");

        self.test_http_get_with_witness()?;
        self.test_http_get_without_witness()?;
        self.test_file_read_with_witness()?;
        self.test_file_read_without_witness()?;
        self.test_policy_adapter_integration()?;
        self.test_epoch_validation()?;

        println!("\n🎉 All adapter integration tests passed!");
        Ok(())
    }
}

#[test]
fn test_adapter_integration() -> Result<(), Box<dyn std::error::Error>> {
    let test_suite = AdapterIntegrationTest::new();
    test_suite.run_all_tests()
}

#[test]
fn test_witness_pipeline() -> Result<(), Box<dyn std::error::Error>> {
    println!("🔒 Testing witness pipeline...");

    // Create a test with high-assurance mode
    let config = PolicyConfig {
        enforcement_mode: EnforcementMode::Enforce,
        shadow_mode: false,
        epoch_validation: true,
        witness_validation: true,
        high_assurance_mode: true,
    };

    let policy_adapter = PolicyAdapter::new(config);

    // Test that operations without witnesses are blocked in high-assurance mode
    let principal = Principal {
        id: "test-user".to_string(),
        roles: vec!["reader".to_string()],
        org: "test-org".to_string(),
    };

    let context = Ctx {
        session: "session-1".to_string(),
        epoch: 1,
        attributes: vec![],
        tenant: "test-tenant".to_string(),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs(),
    };

    let read_action = Action::Read {
        doc: DocId {
            uri: "https://api.example.com/users".to_string(),
            version: 1,
        },
        path: vec!["users".to_string()],
    };

    let result = policy_adapter.evaluate_permission(
        &principal,
        &read_action,
        &context,
        None, // No world state provided
    )?;

    // In high-assurance mode without world state, this should fail
    assert!(!result.allowed);
    assert_eq!(result.permit_decision, "reject");

    println!("✅ Witness pipeline test passed");
    Ok(())
}

#[test]
fn test_resource_mapping_validation() -> Result<(), Box<dyn std::error::Error>> {
    println!("🗺️ Testing resource mapping validation...");

    // Test valid resource mapping
    let valid_resource = MockHttpGetResource {
        doc_id: "https://api.example.com/data".to_string(),
        field_path: vec!["users".to_string()],
        merkle_root: "valid_merkle_root".to_string(),
        field_commit: "valid_commit_hash".to_string(),
        label: "internal".to_string(),
    };

    let http_adapter = MockHttpGetAdapter::new(Some(valid_resource), true, true);

    let witness = MockHttpGetWitness {
        merkle_path: vec!["root".to_string(), "users".to_string()],
        field_commit: "valid_commit_hash".to_string(),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_secs(),
        signature: "valid_signature".to_string(),
    };

    let response = http_adapter.execute("https://api.example.com/data", Some(&witness))?;
    assert!(response.resource_access.access_granted);

    // Test invalid resource mapping (mismatched field commit)
    let invalid_resource = MockHttpGetResource {
        doc_id: "https://api.example.com/data".to_string(),
        field_path: vec!["users".to_string()],
        merkle_root: "valid_merkle_root".to_string(),
        field_commit: "different_commit_hash".to_string(), // Different hash
        label: "internal".to_string(),
    };

    let http_adapter_invalid = MockHttpGetAdapter::new(Some(invalid_resource), true, true);

    let result = http_adapter_invalid.execute("https://api.example.com/data", Some(&witness));
    assert!(result.is_err());
    assert!(result
        .unwrap_err()
        .to_string()
        .contains("Resource access validation failed"));

    println!("✅ Resource mapping validation test passed");
    Ok(())
}
