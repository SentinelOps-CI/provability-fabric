// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use super::ratelimit::*;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::test]
async fn test_rate_limiter_creation() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    assert!(limiter.usage_tracker.read().await.tool_usage.is_empty());
    assert!(limiter.usage_tracker.read().await.tenant_usage.is_empty());
    assert!(limiter.usage_tracker.read().await.global_usage.is_empty());
}

#[tokio::test]
async fn test_basic_rate_limiting() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    // First request should be allowed
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Allow));
    
    // Multiple rapid requests should still be allowed within limits
    for _ in 0..50 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
}

#[tokio::test]
async fn test_tool_specific_limits() {
    let mut config = RateLimitConfig::default();
    
    // Set strict limits for data_query tool
    config.tool_limits.insert("data_query".to_string(), ToolRateLimit {
        tool_name: "data_query".to_string(),
        requests_per_minute: 10, // Very low limit for testing
        requests_per_hour: 100,
        requests_per_day: 1000,
        burst_multiplier: 1.0, // No burst allowance
        requires_approval_above: 5,
    });
    
    let limiter = RateLimiter::new(config);
    
    // First 10 requests should be allowed
    for _ in 0..10 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 11th request should be denied
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_tenant_limits() {
    let mut config = RateLimitConfig::default();
    
    // Set tenant-specific limits
    config.tenant_limits.insert("tenant1".to_string(), TenantRateLimit {
        tenant_id: "tenant1".to_string(),
        total_requests_per_minute: 5,
        total_requests_per_hour: 50,
        total_requests_per_day: 500,
        budget_per_minute: 10.0,
        budget_per_hour: 100.0,
        budget_per_day: 1000.0,
    });
    
    let limiter = RateLimiter::new(config);
    
    // First 5 requests should be allowed
    for _ in 0..5 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 6th request should be denied due to tenant limit
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_approval_threshold() {
    let mut config = RateLimitConfig::default();
    
    // Set approval threshold
    config.tool_limits.insert("data_query".to_string(), ToolRateLimit {
        tool_name: "data_query".to_string(),
        requests_per_minute: 100,
        requests_per_hour: 1000,
        requests_per_day: 10000,
        burst_multiplier: 2.0,
        requires_approval_above: 10, // Require approval above 10 requests
    });
    
    let limiter = RateLimiter::new(config);
    
    // First 10 requests should be allowed
    for _ in 0..10 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 11th request should require approval
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::RequireApproval(_)));
}

#[tokio::test]
async fn test_global_limits() {
    let mut config = RateLimitConfig::default();
    
    // Set very low global limits
    config.global_limits = GlobalRateLimit {
        max_requests_per_minute: 5,
        max_requests_per_hour: 50,
        max_requests_per_day: 500,
        max_concurrent_sessions: 10,
        emergency_threshold: 0.8,
    };
    
    let limiter = RateLimiter::new(config);
    
    // First 5 requests should be allowed
    for _ in 0..5 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 6th request should be denied due to global limit
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_time_window_cleanup() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    // Make some requests
    for _ in 0..5 {
        let _ = limiter.check_rate_limit("tenant1", "data_query", "session1").await;
    }
    
    // Wait for cleanup (simulate time passing)
    sleep(Duration::from_millis(100)).await;
    
    // The usage should still be tracked for the current window
    let usage = limiter.get_current_usage("tenant1", "data_query").await.unwrap();
    assert_eq!(usage.requests_last_minute, 5);
}

#[tokio::test]
async fn test_violation_logging() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    // Log a violation
    let usage = RateLimitUsage {
        requests_last_minute: 150,
        requests_last_hour: 1000,
        requests_last_day: 50000,
        budget_consumed_last_minute: 0.0,
        budget_consumed_last_hour: 0.0,
        budget_consumed_last_day: 0.0,
    };
    
    limiter.log_violation(
        "tenant1",
        "data_query",
        "RATE_LIMIT_EXCEEDED",
        "Too many requests",
        &usage
    ).await.unwrap();
    
    // Check violation stats
    let stats = limiter.get_violation_stats().await.unwrap();
    assert_eq!(stats.get("RATE_LIMIT_EXCEEDED"), Some(&1));
}

#[tokio::test]
async fn test_burst_allowance() {
    let mut config = RateLimitConfig::default();
    
    // Set burst allowance
    config.tool_limits.insert("data_query".to_string(), ToolRateLimit {
        tool_name: "data_query".to_string(),
        requests_per_minute: 10,
        requests_per_hour: 100,
        requests_per_day: 1000,
        burst_multiplier: 2.0, // Allow burst up to 2x
        requires_approval_above: 15,
    });
    
    let limiter = RateLimiter::new(config);
    
    // First 20 requests should be allowed (10 * 2.0 burst)
    for _ in 0..20 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 21st request should be denied
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_config_update() {
    let config = RateLimitConfig::default();
    let mut limiter = RateLimiter::new(config);
    
    // Create new config with different limits
    let mut new_config = RateLimitConfig::default();
    new_config.tool_limits.insert("data_query".to_string(), ToolRateLimit {
        tool_name: "data_query".to_string(),
        requests_per_minute: 5, // Much lower limit
        requests_per_hour: 50,
        requests_per_day: 500,
        burst_multiplier: 1.0,
        requires_approval_above: 3,
    });
    
    // Update configuration
    limiter.update_config(new_config).await.unwrap();
    
    // Test with new limits
    for _ in 0..5 {
        let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    
    // 6th request should be denied with new limits
    let decision = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_multiple_tenants() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    // Make requests for different tenants
    let decision1 = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    let decision2 = limiter.check_rate_limit("tenant2", "data_query", "session2").await.unwrap();
    
    assert!(matches!(decision1, RateLimitDecision::Allow));
    assert!(matches!(decision2, RateLimitDecision::Allow));
    
    // Each tenant should have separate tracking
    let usage1 = limiter.get_current_usage("tenant1", "data_query").await.unwrap();
    let usage2 = limiter.get_current_usage("tenant2", "data_query").await.unwrap();
    
    assert_eq!(usage1.requests_last_minute, 1);
    assert_eq!(usage2.requests_last_minute, 1);
}

#[tokio::test]
async fn test_multiple_tools() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);
    
    // Make requests for different tools
    let decision1 = limiter.check_rate_limit("tenant1", "data_query", "session1").await.unwrap();
    let decision2 = limiter.check_rate_limit("tenant1", "retrieval", "session1").await.unwrap();
    
    assert!(matches!(decision1, RateLimitDecision::Allow));
    assert!(matches!(decision2, RateLimitDecision::Allow));
    
    // Each tool should have separate tracking
    let usage1 = limiter.get_current_usage("tenant1", "data_query").await.unwrap();
    let usage2 = limiter.get_current_usage("tenant1", "retrieval").await.unwrap();
    
    assert_eq!(usage1.requests_last_minute, 1);
    assert_eq!(usage2.requests_last_minute, 1);
}
