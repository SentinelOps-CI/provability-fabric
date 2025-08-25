// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use provability_fabric::policy_adapter::{
    Action, DocId, PolicyAdapter, PolicyConfig, Principal, Tool, WorldState,
};
use provability_fabric::egress_cert::{
    EgressCertificate, PermissionEvidence, ProofHashes, WitnessVerification,
};
use std::collections::HashMap;

/// Test suite for the unified permission system
pub struct PermissionSystemTestSuite {
    adapter: PolicyAdapter,
    world: WorldState,
}

impl PermissionSystemTestSuite {
    pub fn new() -> Self {
        let config = PolicyConfig {
            enforcement_mode: provability_fabric::policy_adapter::EnforcementMode::Enforce,
            shadow_mode: false,
            epoch_validation: true,
            witness_validation: true,
            high_assurance_mode: true,
        };

        let adapter = PolicyAdapter::new(config);
        let world = WorldState::new(1);

        Self { adapter, world }
    }

    /// Test basic tool access control
    pub fn test_tool_access_control(&self) -> Result<(), String> {
        println!("Testing tool access control...");

        let admin_user = Principal {
            id: "admin".to_string(),
            roles: vec!["admin".to_string()],
            org: "admin-org".to_string(),
        };

        let email_user = Principal {
            id: "email-user".to_string(),
            roles: vec!["email_user".to_string()],
            org: "user-org".to_string(),
        };

        let regular_user = Principal {
            id: "regular-user".to_string(),
            roles: vec!["user".to_string()],
            org: "user-org".to_string(),
        };

        let context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 1,
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        // Test admin access to all tools
        let admin_actions = vec![
            Action::Call { tool: Tool::SendEmail },
            Action::Call { tool: Tool::LogSpend },
            Action::Call { tool: Tool::NetworkCall },
            Action::Call { tool: Tool::FileRead },
            Action::Call { tool: Tool::FileWrite },
        ];

        for action in admin_actions {
            let result = self.adapter.evaluate_permission(&admin_user, &action, &context, Some(&self.world))
                .map_err(|e| format!("Admin permission check failed: {}", e))?;
            
            if !result.allowed {
                return Err(format!("Admin should have access to {:?}", action));
            }
        }

        // Test email user access
        let email_action = Action::Call { tool: Tool::SendEmail };
        let result = self.adapter.evaluate_permission(&email_user, &email_action, &context, Some(&self.world))
            .map_err(|e| format!("Email user permission check failed: {}", e))?;
        
        if !result.allowed {
            return Err("Email user should have access to SendEmail".to_string());
        }

        // Test regular user access denial
        let network_action = Action::Call { tool: Tool::NetworkCall };
        let result = self.adapter.evaluate_permission(&regular_user, &network_action, &context, Some(&self.world))
            .map_err(|e| format!("Regular user permission check failed: {}", e))?;
        
        if result.allowed {
            return Err("Regular user should not have access to NetworkCall".to_string());
        }

        println!("✅ Tool access control tests passed");
        Ok(())
    }

    /// Test IFC-aware document operations
    pub fn test_ifc_document_operations(&self) -> Result<(), String> {
        println!("Testing IFC-aware document operations...");

        let mut world = self.world.clone();
        
        // Add test document with labels
        let doc = DocId {
            uri: "test://doc1".to_string(),
            version: 1,
        };

        let doc_state = provability_fabric::policy_adapter::DocumentState::new(
            "owner1".to_string(),
            "merkle_root_123".to_string(),
        );

        world.add_document(&doc, doc_state);
        world.add_labels(&doc, vec!["confidential".to_string()]);

        let reader_user = Principal {
            id: "reader".to_string(),
            roles: vec!["reader".to_string()],
            org: "user-org".to_string(),
        };

        let writer_user = Principal {
            id: "writer".to_string(),
            roles: vec!["writer".to_string()],
            org: "user-org".to_string(),
        };

        let context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 1,
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        // Test read operation with witness validation
        let read_action = Action::Read {
            doc: doc.clone(),
            path: vec!["field1".to_string()],
        };

        let result = self.adapter.evaluate_permission(&reader_user, &read_action, &context, Some(&world))
            .map_err(|e| format!("Read permission check failed: {}", e))?;
        
        if !result.allowed {
            return Err("Reader should have access to read document".to_string());
        }

        if !result.path_witness_ok {
            return Err("Path witness validation should pass".to_string());
        }

        // Test write operation
        let write_action = Action::Write {
            doc: doc.clone(),
            path: vec!["field1".to_string()],
        };

        let result = self.adapter.evaluate_permission(&writer_user, &write_action, &context, Some(&world))
            .map_err(|e| format!("Write permission check failed: {}", e))?;
        
        if !result.allowed {
            return Err("Writer should have access to write document".to_string());
        }

        // Test unauthorized access
        let unauthorized_user = Principal {
            id: "unauthorized".to_string(),
            roles: vec!["user".to_string()],
            org: "user-org".to_string(),
        };

        let result = self.adapter.evaluate_permission(&unauthorized_user, &read_action, &context, Some(&world))
            .map_err(|e| format!("Unauthorized user permission check failed: {}", e))?;
        
        if result.allowed {
            return Err("Unauthorized user should not have access".to_string());
        }

        println!("✅ IFC document operations tests passed");
        Ok(())
    }

    /// Test epoch validation and revocation
    pub fn test_epoch_validation(&self) -> Result<(), String> {
        println!("Testing epoch validation...");

        let mut world = WorldState::new(5); // Start at epoch 5
        
        let user = Principal {
            id: "test-user".to_string(),
            roles: vec!["admin".to_string()],
            org: "test-org".to_string(),
        };

        let action = Action::Call { tool: Tool::SendEmail };

        // Test valid epoch
        let valid_context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 5, // Current epoch
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        let result = self.adapter.evaluate_permission(&user, &action, &valid_context, Some(&world))
            .map_err(|e| format!("Valid epoch permission check failed: {}", e))?;
        
        if !result.allowed {
            return Err("User should have access with valid epoch".to_string());
        }

        // Test expired epoch
        let expired_context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 20, // Too far from current epoch
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        let result = self.adapter.evaluate_permission(&user, &action, &expired_context, Some(&world))
            .map_err(|e| format!("Expired epoch permission check failed: {}", e))?;
        
        if result.allowed {
            return Err("User should not have access with expired epoch".to_string());
        }

        println!("✅ Epoch validation tests passed");
        Ok(())
    }

    /// Test high-assurance mode witness validation
    pub fn test_high_assurance_mode(&self) -> Result<(), String> {
        println!("Testing high-assurance mode...");

        let mut world = WorldState::new(1);
        
        let user = Principal {
            id: "test-user".to_string(),
            roles: vec!["reader".to_string()],
            org: "test-org".to_string(),
        };

        let doc = DocId {
            uri: "test://doc2".to_string(),
            version: 1,
        };

        let context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 1,
            attributes: vec![],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        // Test read without witness (should fail in high-assurance mode)
        let read_action = Action::Read {
            doc: doc.clone(),
            path: vec!["field1".to_string()],
        };

        let result = self.adapter.evaluate_permission(&user, &read_action, &context, Some(&world))
            .map_err(|e| format!("High-assurance mode permission check failed: {}", e))?;
        
        if result.allowed {
            return Err("Read should be denied without witness in high-assurance mode".to_string());
        }

        if result.path_witness_ok {
            return Err("Path witness should be invalid without document in world".to_string());
        }

        // Add document to world and test again
        let doc_state = provability_fabric::policy_adapter::DocumentState::new(
            "owner1".to_string(),
            "merkle_root_456".to_string(),
        );

        world.add_document(&doc, doc_state);
        world.add_labels(&doc, vec!["public".to_string()]);

        let result = self.adapter.evaluate_permission(&user, &read_action, &context, Some(&world))
            .map_err(|e| format!("High-assurance mode permission check with witness failed: {}", e))?;
        
        if !result.allowed {
            return Err("Read should be allowed with valid witness".to_string());
        }

        if !result.path_witness_ok {
            return Err("Path witness should be valid with document in world".to_string());
        }

        println!("✅ High-assurance mode tests passed");
        Ok(())
    }

    /// Test certificate generation with permission evidence
    pub fn test_certificate_generation(&self) -> Result<(), String> {
        println!("Testing certificate generation...");

        let cert = EgressCertificate::new(
            "session-1".to_string(),
            "bundle-1".to_string(),
            "plan-hash-123".to_string(),
            "policy-hash-456".to_string(),
        );

        // Verify certificate structure
        if cert.content.metadata.version != "v2.0" {
            return Err("Certificate should be version 2.0".to_string());
        }

        // Test permission evidence
        let evidence = PermissionEvidence {
            permit_decision: "accept".to_string(),
            path_witness_ok: true,
            label_derivation_ok: true,
            epoch: 1,
            principal_id: "user-1".to_string(),
            action_type: "read".to_string(),
            resource_id: "doc://test".to_string(),
            field_path: Some(vec!["field1".to_string()]),
            abac_attributes: HashMap::new(),
            session_attributes: HashMap::new(),
            scope: Some("tenant-a".to_string()),
        };

        let mut cert = cert;
        cert.add_permission_evidence(evidence);

        if cert.content.permission_evidence.permit_decision != "accept" {
            return Err("Permission evidence should be set correctly".to_string());
        }

        // Test proof hashes
        let hashes = ProofHashes {
            automata_hash: "hash123".to_string(),
            labeler_hash: "hash456".to_string(),
            policy_hash: "hash789".to_string(),
            ni_monitor_hash: "hash012".to_string(),
        };

        cert.add_proof_hashes(hashes);

        if cert.content.proof_hashes.automata_hash != "hash123" {
            return Err("Proof hashes should be set correctly".to_string());
        }

        // Test certificate signing
        if let Err(e) = cert.sign("private-key") {
            return Err(format!("Certificate signing failed: {}", e));
        }

        if !cert.signature.is_some() {
            return Err("Certificate should be signed".to_string());
        }

        // Test signature verification
        if let Err(e) = cert.verify_signature() {
            return Err(format!("Certificate signature verification failed: {}", e));
        }

        println!("✅ Certificate generation tests passed");
        Ok(())
    }

    /// Test ABAC attribute evaluation
    pub fn test_abac_attributes(&self) -> Result<(), String> {
        println!("Testing ABAC attributes...");

        let user = Principal {
            id: "test-user".to_string(),
            roles: vec!["user".to_string()],
            org: "test-org".to_string(),
        };

        let context = provability_fabric::policy_adapter::Ctx {
            session: "test-session".to_string(),
            epoch: 1,
            attributes: vec![
                ("project".to_string(), "project-a".to_string()),
                ("environment".to_string(), "production".to_string()),
                ("clearance".to_string(), "secret".to_string()),
            ],
            tenant: "test-tenant".to_string(),
            timestamp: 1234567890,
        };

        // Test basic permission with attributes
        let action = Action::Call { tool: Tool::FileRead };
        
        let result = self.adapter.evaluate_permission(&user, &action, &context, Some(&self.world))
            .map_err(|e| format!("ABAC permission check failed: {}", e))?;
        
        // In this test, the user doesn't have file_user role, so should be denied
        if result.allowed {
            return Err("User without file_user role should be denied".to_string());
        }

        // Test with user that has appropriate role
        let file_user = Principal {
            id: "file-user".to_string(),
            roles: vec!["file_user".to_string()],
            org: "test-org".to_string(),
        };

        let result = self.adapter.evaluate_permission(&file_user, &action, &context, Some(&self.world))
            .map_err(|e| format!("File user ABAC permission check failed: {}", e))?;
        
        if !result.allowed {
            return Err("File user should have access to FileRead".to_string());
        }

        println!("✅ ABAC attributes tests passed");
        Ok(())
    }

    /// Run all tests
    pub fn run_all_tests(&self) -> Result<(), String> {
        println!("Running permission system test suite...\n");

        self.test_tool_access_control()?;
        self.test_ifc_document_operations()?;
        self.test_epoch_validation()?;
        self.test_high_assurance_mode()?;
        self.test_certificate_generation()?;
        self.test_abac_attributes()?;

        println!("\n🎉 All permission system tests passed!");
        Ok(())
    }
}

/// Test data generator for comprehensive testing
pub struct TestDataGenerator;

impl TestDataGenerator {
    /// Generate test principals with various roles
    pub fn generate_test_principals() -> Vec<Principal> {
        vec![
            Principal {
                id: "admin".to_string(),
                roles: vec!["admin".to_string()],
                org: "admin-org".to_string(),
            },
            Principal {
                id: "email-user".to_string(),
                roles: vec!["email_user".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "finance-user".to_string(),
                roles: vec!["finance_user".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "network-user".to_string(),
                roles: vec!["network_user".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "file-user".to_string(),
                roles: vec!["file_user".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "file-writer".to_string(),
                roles: vec!["file_writer".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "reader".to_string(),
                roles: vec!["reader".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "writer".to_string(),
                roles: vec!["writer".to_string(), "user".to_string()],
                org: "user-org".to_string(),
            },
            Principal {
                id: "owner".to_string(),
                roles: vec!["owner".to_string(), "user".to_string()],
                org: "owner_org".to_string(),
            },
        ]
    }

    /// Generate test documents with various labels
    pub fn generate_test_documents() -> Vec<(DocId, Vec<String>)> {
        vec![
            (DocId { uri: "test://public".to_string(), version: 1 }, vec!["public".to_string()]),
            (DocId { uri: "test://internal".to_string(), version: 1 }, vec!["internal".to_string()]),
            (DocId { uri: "test://confidential".to_string(), version: 1 }, vec!["confidential".to_string()]),
            (DocId { uri: "test://secret".to_string(), version: 1 }, vec!["secret".to_string()]),
            (DocId { uri: "test://custom".to_string(), version: 1 }, vec!["custom_label".to_string()]),
        ]
    }

    /// Generate test actions for comprehensive coverage
    pub fn generate_test_actions() -> Vec<Action> {
        let docs = Self::generate_test_documents();
        let mut actions = Vec::new();

        // Tool actions
        actions.push(Action::Call { tool: Tool::SendEmail });
        actions.push(Action::Call { tool: Tool::LogSpend });
        actions.push(Action::Call { tool: Tool::LogAction });
        actions.push(Action::Call { tool: Tool::NetworkCall });
        actions.push(Action::Call { tool: Tool::FileRead });
        actions.push(Action::Call { tool: Tool::FileWrite });
        actions.push(Action::Call { tool: Tool::Custom { name: "CustomTool".to_string() } });

        // Document actions
        for (doc, _) in docs {
            actions.push(Action::Read { doc: doc.clone(), path: vec!["field1".to_string()] });
            actions.push(Action::Read { doc: doc.clone(), path: vec!["field1".to_string(), "subfield".to_string()] });
            actions.push(Action::Write { doc: doc.clone(), path: vec!["field1".to_string()] });
            actions.push(Action::Write { doc: doc.clone(), path: vec!["field1".to_string(), "subfield".to_string()] });
        }

        // Grant actions
        let test_principal = Principal {
            id: "test-grantee".to_string(),
            roles: vec!["user".to_string()],
            org: "test-org".to_string(),
        };

        actions.push(Action::Grant {
            principal: test_principal,
            action: Box::new(Action::Call { tool: Tool::FileRead }),
        });

        actions
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permission_system_suite() {
        let suite = PermissionSystemTestSuite::new();
        suite.run_all_tests().expect("Permission system tests failed");
    }

    #[test]
    fn test_test_data_generation() {
        let principals = TestDataGenerator::generate_test_principals();
        assert!(!principals.is_empty());
        assert!(principals.iter().any(|p| p.roles.contains(&"admin".to_string())));

        let documents = TestDataGenerator::generate_test_documents();
        assert!(!documents.is_empty());
        assert!(documents.iter().any(|(_, labels)| labels.contains(&"public".to_string())));

        let actions = TestDataGenerator::generate_test_actions();
        assert!(!actions.is_empty());
        assert!(actions.iter().any(|a| matches!(a, Action::Call { tool: Tool::SendEmail })));
    }
}
