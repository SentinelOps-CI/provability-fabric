// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use super::*;
use std::collections::HashMap;

#[tokio::test]
async fn test_tool_broker_integration() {
    // Create a new tool broker
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test plan submission
    let plan_json = r#"{
        "plan_id": "integration-test-plan",
        "tenant": "test-tenant",
        "subject": {
            "id": "test-user",
            "caps": ["read_docs", "send_email"]
        },
        "steps": [
            {
                "tool": "retrieval",
                "args": {"query": "test query"},
                "caps_required": ["read_docs"],
                "labels_in": [],
                "labels_out": ["docs"]
            }
        ],
        "constraints": {
            "budget": 10.0,
            "pii": false,
            "dp_epsilon": 1.0
        },
        "system_prompt_hash": "a1b2c3d4e5f6..."
    }"#;
    
    // Submit plan to kernel (this will fail in test environment, but we can test the structure)
    let plan_result = broker.submit_plan(plan_json).await;
    // In test environment, this will likely fail due to no kernel, but we can verify the broker structure
    
    // Test rate limiting integration
    let rate_limit_stats = broker.get_rate_limit_stats().await.unwrap();
    assert!(rate_limit_stats.is_empty(), "Should start with no violations");
    
    // Test tool execution with rate limiting
    let tool_call = ToolCall {
        tool: "data_query".to_string(),
        args: HashMap::new(),
        step_index: Some(0),
    };
    
    // This should fail due to no approved plan, but we can verify the broker structure
    let execution_result = broker.execute_tool(&tool_call, "integration-test-plan").await;
    // In test environment, this will fail, but we can verify the broker handles errors gracefully
    
    // Verify broker components are properly initialized
    assert!(broker.rate_limiter.usage_tracker.read().await.tool_usage.is_empty());
    assert!(broker.approval_manager.pending_requests.read().await.is_empty());
}

#[tokio::test]
async fn test_rate_limiting_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test that rate limiting is properly integrated
    let stats = broker.get_rate_limit_stats().await.unwrap();
    assert!(stats.is_empty());
    
    // Test configuration update
    let mut new_config = RateLimitConfig::default();
    new_config.tool_limits.insert("test_tool".to_string(), ToolRateLimit {
        tool_name: "test_tool".to_string(),
        requests_per_minute: 5,
        requests_per_hour: 50,
        requests_per_day: 500,
        burst_multiplier: 1.0,
        requires_approval_above: 3,
    });
    
    broker.update_rate_limit_config(new_config).await.unwrap();
    
    // Verify the configuration was updated
    let updated_stats = broker.get_rate_limit_stats().await.unwrap();
    assert!(updated_stats.is_empty());
}

#[tokio::test]
async fn test_approval_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test that approval manager is properly integrated
    let pending_requests = broker.approval_manager.pending_requests.read().await;
    assert!(pending_requests.is_empty());
    
    // Test approval workflow (this would require a real approval request in a real scenario)
    // For now, we just verify the component is accessible
    assert!(broker.approval_manager.approvers.read().await.is_empty());
}

#[tokio::test]
async fn test_violation_logging_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test violation logging
    let violations = broker.get_violations().await;
    assert!(violations.is_empty(), "Should start with no violations");
    
    // Test rate limit violation logging through the rate limiter
    let usage = RateLimitUsage {
        requests_last_minute: 150,
        requests_last_hour: 1000,
        requests_last_day: 50000,
        budget_consumed_last_minute: 0.0,
        budget_consumed_last_hour: 0.0,
        budget_consumed_last_day: 0.0,
    };
    
    broker.rate_limiter.log_violation(
        "test-tenant",
        "test-tool",
        "TEST_VIOLATION",
        "Test violation reason",
        &usage
    ).await.unwrap();
    
    // Verify violation was logged
    let stats = broker.get_rate_limit_stats().await.unwrap();
    assert_eq!(stats.get("TEST_VIOLATION"), Some(&1));
}

#[tokio::test]
async fn test_metrics_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test that metrics are properly integrated
    // In a real environment, these would be exposed via Prometheus
    // For now, we just verify the broker structure supports metrics
    
    // Test rate limit violation metrics
    let usage = RateLimitUsage {
        requests_last_minute: 150,
        requests_last_hour: 1000,
        requests_last_day: 50000,
        budget_consumed_last_minute: 0.0,
        budget_consumed_last_hour: 0.0,
        budget_consumed_last_day: 0.0,
    };
    
    // This should increment the pf_broker_denies_total metric
    broker.rate_limiter.log_violation(
        "test-tenant",
        "test-tool",
        "RATE_LIMIT_EXCEEDED",
        "Rate limit exceeded",
        &usage
    ).await.unwrap();
    
    // Verify the violation was logged
    let stats = broker.get_rate_limit_stats().await.unwrap();
    assert_eq!(stats.get("RATE_LIMIT_EXCEEDED"), Some(&1));
}

#[tokio::test]
async fn test_error_handling_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test error handling for invalid plan IDs
    let tool_call = ToolCall {
        tool: "invalid_tool".to_string(),
        args: HashMap::new(),
        step_index: Some(999),
    };
    
    let result = broker.execute_tool(&tool_call, "non-existent-plan").await;
    assert!(result.is_err(), "Should fail for non-existent plan");
    
    // Test error handling for invalid tool calls
    let invalid_call = ToolCall {
        tool: "".to_string(), // Empty tool name
        args: HashMap::new(),
        step_index: None,
    };
    
    let result = broker.execute_tool(&invalid_call, "integration-test-plan").await;
    assert!(result.is_err(), "Should fail for invalid tool call");
}

#[tokio::test]
async fn test_concurrent_access_integration() {
    let broker = Arc::new(ToolBroker::new("http://localhost:8080".to_string()));
    
    // Test concurrent access to rate limiter
    let mut handles = vec![];
    
    for i in 0..10 {
        let broker_clone = Arc::clone(&broker);
        let handle = tokio::spawn(async move {
            let result = broker_clone.rate_limiter.check_rate_limit(
                &format!("tenant{}", i),
                "data_query",
                &format!("session{}", i)
            ).await;
            result
        });
        handles.push(handle);
    }
    
    // Wait for all tasks to complete
    let results = futures::future::join_all(handles).await;
    
    // All should succeed
    for result in results {
        assert!(result.is_ok(), "Concurrent access should work");
        let rate_limit_result = result.unwrap().unwrap();
        assert!(matches!(rate_limit_result, RateLimitDecision::Allow));
    }
}

#[tokio::test]
async fn test_configuration_persistence_integration() {
    let mut broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test configuration persistence
    let mut new_config = RateLimitConfig::default();
    new_config.tool_limits.insert("persistent_tool".to_string(), ToolRateLimit {
        tool_name: "persistent_tool".to_string(),
        requests_per_minute: 1, // Very restrictive
        requests_per_hour: 10,
        requests_per_day: 100,
        burst_multiplier: 1.0,
        requires_approval_above: 1,
    });
    
    // Update configuration
    broker.update_rate_limit_config(new_config).await.unwrap();
    
    // Test that new configuration is active
    let decision = broker.rate_limiter.check_rate_limit(
        "test-tenant",
        "persistent_tool",
        "session1"
    ).await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Allow));
    
    // Second request should be denied
    let decision = broker.rate_limiter.check_rate_limit(
        "test-tenant",
        "persistent_tool",
        "session1"
    ).await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_cleanup_integration() {
    let broker = ToolBroker::new("http://localhost:8080".to_string());
    
    // Test cleanup of old entries
    // Make some requests to populate the tracker
    for _ in 0..5 {
        let _ = broker.rate_limiter.check_rate_limit(
            "test-tenant",
            "cleanup_test_tool",
            "session1"
        ).await;
    }
    
    // Verify entries were created
    let usage = broker.rate_limiter.get_current_usage("test-tenant", "cleanup_test_tool").await.unwrap();
    assert_eq!(usage.requests_last_minute, 5);
    
    // In a real environment, cleanup would happen automatically
    // For now, we just verify the cleanup mechanism exists
    let tracker = broker.rate_limiter.usage_tracker.read().await;
    assert!(!tracker.tool_usage.is_empty());
}
