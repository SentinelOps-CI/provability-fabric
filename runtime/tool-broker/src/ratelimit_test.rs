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

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Allow));

    for _ in 0..40 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
}

#[tokio::test]
async fn test_tool_specific_limits() {
    let mut config = RateLimitConfig::default();
    config.throttle_delay_ms = 1;
    config.tool_limits.insert(
        "data_query".to_string(),
        ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 10,
            requests_per_hour: 100,
            requests_per_day: 1000,
            burst_multiplier: 1.0,
            requires_approval_above: 100,
            cost_per_request: 1.0,
            risk_score: 0.5,
        },
    );

    let limiter = RateLimiter::new(config);

    for _ in 0..10 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(
            decision,
            RateLimitDecision::Allow | RateLimitDecision::Throttle(_)
        ));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_tenant_limits() {
    let mut config = RateLimitConfig::default();
    config.tenant_limits.insert(
        "tenant1".to_string(),
        TenantRateLimit {
            tenant_id: "tenant1".to_string(),
            total_requests_per_minute: 5,
            total_requests_per_hour: 50,
            total_requests_per_day: 500,
            budget_per_minute: 10.0,
            budget_per_hour: 100.0,
            budget_per_day: 1000.0,
        },
    );

    let limiter = RateLimiter::new(config);

    for _ in 0..5 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_approval_threshold() {
    let mut config = RateLimitConfig::default();
    config.tool_limits.insert(
        "data_query".to_string(),
        ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 100,
            requests_per_hour: 1000,
            requests_per_day: 10000,
            burst_multiplier: 2.0,
            requires_approval_above: 10,
            cost_per_request: 1.0,
            risk_score: 0.5,
        },
    );

    let limiter = RateLimiter::new(config);

    for _ in 0..10 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::RequireApproval(_)));
}

#[tokio::test]
async fn test_global_limits() {
    let mut config = RateLimitConfig::default();
    config.global_limits = GlobalRateLimit {
        max_requests_per_minute: 5,
        max_requests_per_hour: 50,
        max_requests_per_day: 500,
        max_concurrent_sessions: 10,
        emergency_threshold: 0.8,
    };

    let limiter = RateLimiter::new(config);

    for _ in 0..5 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_time_window_cleanup() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);

    for _ in 0..5 {
        let _ = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await;
    }

    sleep(Duration::from_millis(100)).await;

    let usage = limiter
        .get_current_usage("tenant1", "data_query")
        .await
        .unwrap();
    assert_eq!(usage.requests_last_minute, 5);
}

#[tokio::test]
async fn test_violation_logging() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);

    let usage = RateLimitUsage {
        requests_last_minute: 150,
        requests_last_hour: 1000,
        requests_last_day: 50000,
        budget_consumed_last_minute: 0.0,
        budget_consumed_last_hour: 0.0,
        budget_consumed_last_day: 0.0,
    };

    limiter
        .log_violation(
            "tenant1",
            "data_query",
            "RATE_LIMIT_EXCEEDED",
            "Too many requests",
            &usage,
        )
        .await
        .unwrap();

    let stats = limiter.get_violation_stats().await.unwrap();
    assert_eq!(stats.get("RATE_LIMIT_EXCEEDED"), Some(&1));
}

#[tokio::test]
async fn test_burst_allowance() {
    let mut config = RateLimitConfig::default();
    config.throttle_delay_ms = 1;
    config.tool_limits.insert(
        "data_query".to_string(),
        ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 10,
            requests_per_hour: 100,
            requests_per_day: 1000,
            burst_multiplier: 2.0,
            requires_approval_above: 100,
            cost_per_request: 1.0,
            risk_score: 0.5,
        },
    );

    let limiter = RateLimiter::new(config);

    // Soft=10, burst=20: first 10 Allow, next 10 Throttle, then Deny
    for _ in 0..10 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Allow));
    }
    for _ in 0..10 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(decision, RateLimitDecision::Throttle(_)));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_config_update() {
    let config = RateLimitConfig::default();
    let mut limiter = RateLimiter::new(config);

    let mut new_config = RateLimitConfig::default();
    new_config.tool_limits.insert(
        "data_query".to_string(),
        ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 5,
            requests_per_hour: 50,
            requests_per_day: 500,
            burst_multiplier: 1.0,
            requires_approval_above: 100,
            cost_per_request: 1.0,
            risk_score: 0.5,
        },
    );

    limiter.update_config(new_config).await.unwrap();

    for _ in 0..5 {
        let decision = limiter
            .check_rate_limit("tenant1", "data_query", "session1")
            .await
            .unwrap();
        assert!(matches!(
            decision,
            RateLimitDecision::Allow | RateLimitDecision::Throttle(_)
        ));
    }

    let decision = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    assert!(matches!(decision, RateLimitDecision::Deny(_)));
}

#[tokio::test]
async fn test_multiple_tenants() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);

    let decision1 = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    let decision2 = limiter
        .check_rate_limit("tenant2", "data_query", "session2")
        .await
        .unwrap();

    assert!(matches!(decision1, RateLimitDecision::Allow));
    assert!(matches!(decision2, RateLimitDecision::Allow));

    let usage1 = limiter
        .get_current_usage("tenant1", "data_query")
        .await
        .unwrap();
    let usage2 = limiter
        .get_current_usage("tenant2", "data_query")
        .await
        .unwrap();

    assert_eq!(usage1.requests_last_minute, 1);
    assert_eq!(usage2.requests_last_minute, 1);
}

#[tokio::test]
async fn test_multiple_tools() {
    let config = RateLimitConfig::default();
    let limiter = RateLimiter::new(config);

    let decision1 = limiter
        .check_rate_limit("tenant1", "data_query", "session1")
        .await
        .unwrap();
    let decision2 = limiter
        .check_rate_limit("tenant1", "retrieval", "session1")
        .await
        .unwrap();

    assert!(matches!(decision1, RateLimitDecision::Allow));
    assert!(matches!(decision2, RateLimitDecision::Allow));

    let usage1 = limiter
        .get_current_usage("tenant1", "data_query")
        .await
        .unwrap();
    let usage2 = limiter
        .get_current_usage("tenant1", "retrieval")
        .await
        .unwrap();

    assert_eq!(usage1.requests_last_minute, 1);
    assert_eq!(usage2.requests_last_minute, 1);
}

#[tokio::test]
async fn test_budget_consumed_sliding_window() {
    let mut config = RateLimitConfig::default();
    config.tool_limits.insert(
        "metered".to_string(),
        ToolRateLimit {
            tool_name: "metered".to_string(),
            requests_per_minute: 100,
            requests_per_hour: 1000,
            requests_per_day: 10000,
            burst_multiplier: 2.0,
            requires_approval_above: 50,
            cost_per_request: 2.5,
            risk_score: 0.4,
        },
    );

    let limiter = RateLimiter::new(config);

    for _ in 0..4 {
        assert!(matches!(
            limiter
                .check_rate_limit("t1", "metered", "s")
                .await
                .unwrap(),
            RateLimitDecision::Allow
        ));
    }

    let usage = limiter.get_current_usage("t1", "metered").await.unwrap();
    assert!((usage.budget_consumed_last_minute - 10.0).abs() < f64::EPSILON);
    assert!((usage.budget_consumed_last_hour - 10.0).abs() < f64::EPSILON);
    assert!((usage.budget_consumed_last_day - 10.0).abs() < f64::EPSILON);
}

#[tokio::test]
async fn test_budget_exceed_denies() {
    let mut config = RateLimitConfig::default();
    config.tool_limits.insert(
        "pricey".to_string(),
        ToolRateLimit {
            tool_name: "pricey".to_string(),
            requests_per_minute: 1000,
            requests_per_hour: 10000,
            requests_per_day: 100000,
            burst_multiplier: 2.0,
            requires_approval_above: 500,
            cost_per_request: 5.0,
            risk_score: 0.6,
        },
    );
    config.tenant_limits.insert(
        "budget-tenant".to_string(),
        TenantRateLimit {
            tenant_id: "budget-tenant".to_string(),
            total_requests_per_minute: 1000,
            total_requests_per_hour: 10000,
            total_requests_per_day: 100000,
            budget_per_minute: 10.0,
            budget_per_hour: 100.0,
            budget_per_day: 1000.0,
        },
    );

    let limiter = RateLimiter::new(config);

    assert!(matches!(
        limiter
            .check_rate_limit("budget-tenant", "pricey", "s1")
            .await
            .unwrap(),
        RateLimitDecision::Allow
    ));
    assert!(matches!(
        limiter
            .check_rate_limit("budget-tenant", "pricey", "s1")
            .await
            .unwrap(),
        RateLimitDecision::Allow
    ));

    let denied = limiter
        .check_rate_limit("budget-tenant", "pricey", "s1")
        .await
        .unwrap();
    assert!(
        matches!(denied, RateLimitDecision::Deny(ref r) if r.contains("budget exceeded")),
        "got {:?}",
        denied
    );
}

#[tokio::test]
async fn test_tenant_isolation() {
    let mut config = RateLimitConfig::default();
    config.tool_limits.insert(
        "shared".to_string(),
        ToolRateLimit {
            tool_name: "shared".to_string(),
            requests_per_minute: 3,
            requests_per_hour: 100,
            requests_per_day: 1000,
            burst_multiplier: 1.0,
            requires_approval_above: 100,
            cost_per_request: 1.0,
            risk_score: 0.4,
        },
    );

    let limiter = RateLimiter::new(config);

    for _ in 0..3 {
        assert!(matches!(
            limiter
                .check_rate_limit("tenant-a", "shared", "s")
                .await
                .unwrap(),
            RateLimitDecision::Allow | RateLimitDecision::Throttle(_)
        ));
    }

    assert!(matches!(
        limiter
            .check_rate_limit("tenant-a", "shared", "s")
            .await
            .unwrap(),
        RateLimitDecision::Deny(_)
    ));

    assert!(matches!(
        limiter
            .check_rate_limit("tenant-b", "shared", "s")
            .await
            .unwrap(),
        RateLimitDecision::Allow | RateLimitDecision::Throttle(_)
    ));
}

#[tokio::test]
async fn test_throttle_delay_observed() {
    let delay = Duration::from_millis(40);
    let start = std::time::Instant::now();
    // Mirror broker throttle application
    tokio::time::sleep(delay).await;
    assert!(start.elapsed() >= Duration::from_millis(35));

    let mut config = RateLimitConfig::default();
    config.throttle_delay_ms = 20;
    config.tool_limits.insert(
        "soft".to_string(),
        ToolRateLimit {
            tool_name: "soft".to_string(),
            requests_per_minute: 1,
            requests_per_hour: 100,
            requests_per_day: 1000,
            burst_multiplier: 4.0,
            requires_approval_above: 100,
            cost_per_request: 0.1,
            risk_score: 0.2,
        },
    );

    let limiter = RateLimiter::new(config);
    assert!(matches!(
        limiter.check_rate_limit("t", "soft", "s").await.unwrap(),
        RateLimitDecision::Allow
    ));

    match limiter.check_rate_limit("t", "soft", "s").await.unwrap() {
        RateLimitDecision::Throttle(ms) => {
            let start = std::time::Instant::now();
            tokio::time::sleep(Duration::from_millis(ms)).await;
            assert!(start.elapsed() >= Duration::from_millis(ms.saturating_sub(5)));
        }
        other => panic!("expected Throttle, got {:?}", other),
    }
}
