// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::info;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// Rate limit configuration for different tool types and tenants
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitConfig {
    pub tool_limits: HashMap<String, ToolRateLimit>,
    pub tenant_limits: HashMap<String, TenantRateLimit>,
    pub global_limits: GlobalRateLimit,
    pub burst_allowance: f64, // Multiplier for burst capacity
    pub sliding_window_ms: u64, // Sliding window size in milliseconds
    /// Base delay applied when soft limits are exceeded but burst still allows.
    pub throttle_delay_ms: u64,
}

/// Rate limit for a specific tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolRateLimit {
    pub tool_name: String,
    pub requests_per_minute: u32,
    pub requests_per_hour: u32,
    pub requests_per_day: u32,
    pub burst_multiplier: f64, // Allow burst up to this multiple
    pub requires_approval_above: u32, // Require approval above this threshold
    /// Budget cost charged per successful rate-limit admission.
    pub cost_per_request: f64,
    /// Policy risk score in [0.0, 1.0] used when approvals are required.
    pub risk_score: f64,
}

impl ToolRateLimit {
    pub fn with_defaults(tool_name: impl Into<String>) -> Self {
        Self {
            tool_name: tool_name.into(),
            requests_per_minute: 100,
            requests_per_hour: 5000,
            requests_per_day: 100000,
            burst_multiplier: 2.0,
            requires_approval_above: 50,
            cost_per_request: 1.0,
            risk_score: 0.5,
        }
    }
}

/// Rate limit for a specific tenant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TenantRateLimit {
    pub tenant_id: String,
    pub total_requests_per_minute: u32,
    pub total_requests_per_hour: u32,
    pub total_requests_per_day: u32,
    pub budget_per_minute: f64,
    pub budget_per_hour: f64,
    pub budget_per_day: f64,
}

/// Global rate limiting configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GlobalRateLimit {
    pub max_requests_per_minute: u32,
    pub max_requests_per_hour: u32,
    pub max_requests_per_day: u32,
    pub max_concurrent_sessions: u32,
    pub emergency_threshold: f64, // Percentage that triggers emergency mode
}

impl Default for RateLimitConfig {
    fn default() -> Self {
        let mut tool_limits = HashMap::new();

        tool_limits.insert("data_query".to_string(), ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 100,
            requests_per_hour: 5000,
            requests_per_day: 100000,
            burst_multiplier: 2.0,
            requires_approval_above: 50,
            cost_per_request: 1.0,
            risk_score: 0.5,
        });

        tool_limits.insert("retrieval".to_string(), ToolRateLimit {
            tool_name: "retrieval".to_string(),
            requests_per_minute: 200,
            requests_per_hour: 10000,
            requests_per_day: 200000,
            burst_multiplier: 1.5,
            requires_approval_above: 100,
            cost_per_request: 0.5,
            risk_score: 0.3,
        });

        tool_limits.insert("search".to_string(), ToolRateLimit {
            tool_name: "search".to_string(),
            requests_per_minute: 150,
            requests_per_hour: 8000,
            requests_per_day: 150000,
            burst_multiplier: 1.5,
            requires_approval_above: 75,
            cost_per_request: 0.4,
            risk_score: 0.4,
        });

        tool_limits.insert("email".to_string(), ToolRateLimit {
            tool_name: "email".to_string(),
            requests_per_minute: 30,
            requests_per_hour: 500,
            requests_per_day: 5000,
            burst_multiplier: 1.2,
            requires_approval_above: 10,
            cost_per_request: 2.0,
            risk_score: 0.7,
        });

        Self {
            tool_limits,
            tenant_limits: HashMap::new(),
            global_limits: GlobalRateLimit {
                max_requests_per_minute: 10000,
                max_requests_per_hour: 500000,
                max_requests_per_day: 10000000,
                max_concurrent_sessions: 1000,
                emergency_threshold: 0.9,
            },
            burst_allowance: 1.5,
            sliding_window_ms: 60000,
            throttle_delay_ms: 50,
        }
    }
}

/// Rate limit decision
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RateLimitDecision {
    Allow,
    Deny(String), // Reason for denial
    RequireApproval(String), // Reason approval is needed
    Throttle(u64), // Delay in milliseconds
}

/// Rate limit violation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitViolation {
    pub violation_id: String,
    pub tenant_id: String,
    pub tool_name: String,
    pub violation_type: String,
    pub reason: String,
    pub timestamp: DateTime<Utc>,
    pub current_usage: RateLimitUsage,
    pub limits: RateLimitInfo,
}

/// Current rate limit usage
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitUsage {
    pub requests_last_minute: u32,
    pub requests_last_hour: u32,
    pub requests_last_day: u32,
    pub budget_consumed_last_minute: f64,
    pub budget_consumed_last_hour: f64,
    pub budget_consumed_last_day: f64,
}

/// Rate limit information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitInfo {
    pub tool_limit: Option<ToolRateLimit>,
    pub tenant_limit: Option<TenantRateLimit>,
    pub global_limit: GlobalRateLimit,
}

/// Rate limiter implementation
pub struct RateLimiter {
    config: RateLimitConfig,
    /// Exposed for crate-internal tests that assert on usage state.
    pub(crate) usage_tracker: Arc<RwLock<UsageTracker>>,
    violation_log: Arc<RwLock<Vec<RateLimitViolation>>>,
}

/// Single budget consumption event in a sliding window.
#[derive(Debug, Clone)]
pub(crate) struct BudgetEvent {
    pub(crate) at: Instant,
    pub(crate) amount: f64,
}

/// Tracks usage across different time windows. Fields are pub(crate) for crate-internal tests.
pub(crate) struct UsageTracker {
    pub(crate) tool_usage: HashMap<String, HashMap<String, VecDeque<Instant>>>, // tool -> tenant -> timestamps
    pub(crate) tenant_usage: HashMap<String, VecDeque<Instant>>, // tenant -> timestamps
    pub(crate) global_usage: VecDeque<Instant>,
    /// Per-tenant sliding-window budget events.
    pub(crate) budget_usage: HashMap<String, VecDeque<BudgetEvent>>,
}

impl RateLimiter {
    pub fn new(config: RateLimitConfig) -> Self {
        Self {
            config,
            usage_tracker: Arc::new(RwLock::new(UsageTracker::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// Look up policy risk score for a tool from allow-list metadata.
    pub fn risk_score_for_tool(&self, tool_name: &str) -> f64 {
        self.config
            .tool_limits
            .get(tool_name)
            .map(|t| t.risk_score.clamp(0.0, 1.0))
            .unwrap_or(0.9)
    }

    /// Cost charged for one admission of this tool.
    pub fn cost_for_tool(&self, tool_name: &str) -> f64 {
        self.config
            .tool_limits
            .get(tool_name)
            .map(|t| t.cost_per_request.max(0.0))
            .unwrap_or(1.0)
    }

    /// Check if a request is allowed based on rate limits
    pub async fn check_rate_limit(
        &self,
        tenant_id: &str,
        tool_name: &str,
        _session_id: &str,
    ) -> Result<RateLimitDecision> {
        let start_time = Instant::now();

        let usage = self.get_current_usage(tenant_id, tool_name).await?;

        if let RateLimitDecision::Deny(reason) = self.check_global_limits(&usage).await? {
            return Ok(RateLimitDecision::Deny(reason));
        }

        if let RateLimitDecision::Deny(reason) = self.check_tenant_limits(tenant_id, &usage).await? {
            return Ok(RateLimitDecision::Deny(reason));
        }

        match self.check_tool_limits(tool_name, tenant_id, &usage).await? {
            RateLimitDecision::Deny(reason) => {
                return Ok(RateLimitDecision::Deny(reason));
            }
            RateLimitDecision::Throttle(delay_ms) => {
                self.record_usage(tenant_id, tool_name).await?;
                return Ok(RateLimitDecision::Throttle(delay_ms));
            }
            RateLimitDecision::RequireApproval(reason) => {
                return Ok(RateLimitDecision::RequireApproval(reason));
            }
            RateLimitDecision::Allow => {}
        }

        if let Some(approval_reason) = self.check_approval_required(tool_name, tenant_id, &usage).await? {
            return Ok(RateLimitDecision::RequireApproval(approval_reason));
        }

        self.record_usage(tenant_id, tool_name).await?;

        let processing_time = start_time.elapsed();
        info!(
            "Rate limit check completed in {:?} for tenant={}, tool={}",
            processing_time, tenant_id, tool_name
        );

        Ok(RateLimitDecision::Allow)
    }

    /// Check global rate limits
    async fn check_global_limits(&self, usage: &RateLimitUsage) -> Result<RateLimitDecision> {
        let _tracker = self.usage_tracker.read().await;

        if usage.requests_last_minute >= self.config.global_limits.max_requests_per_minute {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for minute".to_string()
            ));
        }

        if usage.requests_last_hour >= self.config.global_limits.max_requests_per_hour {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for hour".to_string()
            ));
        }

        if usage.requests_last_day >= self.config.global_limits.max_requests_per_day {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for day".to_string()
            ));
        }

        Ok(RateLimitDecision::Allow)
    }

    /// Check tenant-specific rate limits (request counts + budget sliding windows)
    async fn check_tenant_limits(&self, tenant_id: &str, usage: &RateLimitUsage) -> Result<RateLimitDecision> {
        let tracker = self.usage_tracker.read().await;
        let tenant_timestamps = tracker
            .tenant_usage
            .get(tenant_id)
            .cloned()
            .unwrap_or_default();

        let tenant_minute = tracker.get_requests_in_window(&tenant_timestamps, Duration::from_secs(60));
        let tenant_hour = tracker.get_requests_in_window(&tenant_timestamps, Duration::from_secs(3600));
        let tenant_day = tracker.get_requests_in_window(&tenant_timestamps, Duration::from_secs(86400));

        if let Some(tenant_limit) = self.config.tenant_limits.get(tenant_id) {
            if tenant_minute >= tenant_limit.total_requests_per_minute {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for minute: {}", tenant_id)
                ));
            }

            if tenant_hour >= tenant_limit.total_requests_per_hour {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for hour: {}", tenant_id)
                ));
            }

            if tenant_day >= tenant_limit.total_requests_per_day {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for day: {}", tenant_id)
                ));
            }

            if usage.budget_consumed_last_minute >= tenant_limit.budget_per_minute {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant budget exceeded for minute: {}", tenant_id)
                ));
            }

            if usage.budget_consumed_last_hour >= tenant_limit.budget_per_hour {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant budget exceeded for hour: {}", tenant_id)
                ));
            }

            if usage.budget_consumed_last_day >= tenant_limit.budget_per_day {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant budget exceeded for day: {}", tenant_id)
                ));
            }
        }

        Ok(RateLimitDecision::Allow)
    }

    /// Check tool-specific rate limits.
    /// Soft limit exceeded (but within burst) → Throttle; burst exceeded → Deny.
    async fn check_tool_limits(
        &self,
        tool_name: &str,
        _tenant_id: &str,
        usage: &RateLimitUsage,
    ) -> Result<RateLimitDecision> {
        if let Some(tool_limit) = self.config.tool_limits.get(tool_name) {
            let soft_limit = tool_limit.requests_per_minute;
            let burst_limit =
                ((tool_limit.requests_per_minute as f64) * tool_limit.burst_multiplier).floor() as u32;
            let burst_limit = burst_limit.max(soft_limit);

            if usage.requests_last_minute >= burst_limit {
                return Ok(RateLimitDecision::Deny(format!(
                    "Tool burst limit exceeded: {} >= {}",
                    usage.requests_last_minute, burst_limit
                )));
            }

            if usage.requests_last_minute >= soft_limit {
                let over = usage.requests_last_minute.saturating_sub(soft_limit.saturating_sub(1));
                let delay_ms = self.config.throttle_delay_ms.saturating_mul(over.max(1) as u64);
                return Ok(RateLimitDecision::Throttle(delay_ms));
            }
        }

        Ok(RateLimitDecision::Allow)
    }

    /// Check if approval is required based on usage patterns
    async fn check_approval_required(
        &self,
        tool_name: &str,
        _tenant_id: &str,
        usage: &RateLimitUsage,
    ) -> Result<Option<String>> {
        if let Some(tool_limit) = self.config.tool_limits.get(tool_name) {
            if usage.requests_last_minute >= tool_limit.requires_approval_above
                && tool_limit.requires_approval_above < tool_limit.requests_per_minute
            {
                return Ok(Some(format!(
                    "Usage {} exceeds approval threshold {} for tool {}",
                    usage.requests_last_minute,
                    tool_limit.requires_approval_above,
                    tool_name
                )));
            }
        }

        Ok(None)
    }

    /// Get current usage statistics including sliding-window budget consumption.
    pub async fn get_current_usage(&self, tenant_id: &str, tool_name: &str) -> Result<RateLimitUsage> {
        let tracker = self.usage_tracker.read().await;

        let tool_timestamps = tracker
            .tool_usage
            .get(tool_name)
            .and_then(|t| t.get(tenant_id))
            .cloned()
            .unwrap_or_default();

        let requests_last_minute =
            tracker.get_requests_in_window(&tool_timestamps, Duration::from_secs(60));
        let requests_last_hour =
            tracker.get_requests_in_window(&tool_timestamps, Duration::from_secs(3600));
        let requests_last_day =
            tracker.get_requests_in_window(&tool_timestamps, Duration::from_secs(86400));

        let budget_events = tracker
            .budget_usage
            .get(tenant_id)
            .cloned()
            .unwrap_or_default();

        let budget_consumed_last_minute =
            tracker.get_budget_in_window(&budget_events, Duration::from_secs(60));
        let budget_consumed_last_hour =
            tracker.get_budget_in_window(&budget_events, Duration::from_secs(3600));
        let budget_consumed_last_day =
            tracker.get_budget_in_window(&budget_events, Duration::from_secs(86400));

        Ok(RateLimitUsage {
            requests_last_minute,
            requests_last_hour,
            requests_last_day,
            budget_consumed_last_minute,
            budget_consumed_last_hour,
            budget_consumed_last_day,
        })
    }

    /// Record usage (request timestamps + budget cost) for sliding-window accounting.
    pub async fn record_usage(&self, tenant_id: &str, tool_name: &str) -> Result<()> {
        let cost = self.cost_for_tool(tool_name);
        let mut tracker = self.usage_tracker.write().await;
        let now = Instant::now();

        tracker
            .tool_usage
            .entry(tool_name.to_string())
            .or_default()
            .entry(tenant_id.to_string())
            .or_default()
            .push_back(now);

        tracker
            .tenant_usage
            .entry(tenant_id.to_string())
            .or_default()
            .push_back(now);

        tracker.global_usage.push_back(now);

        tracker
            .budget_usage
            .entry(tenant_id.to_string())
            .or_default()
            .push_back(BudgetEvent {
                at: now,
                amount: cost,
            });

        tracker.cleanup_old_entries();

        Ok(())
    }

    /// Log rate limit violation
    pub async fn log_violation(
        &self,
        tenant_id: &str,
        tool_name: &str,
        violation_type: &str,
        reason: &str,
        usage: &RateLimitUsage,
    ) -> Result<()> {
        let violation = RateLimitViolation {
            violation_id: Uuid::new_v4().to_string(),
            tenant_id: tenant_id.to_string(),
            tool_name: tool_name.to_string(),
            violation_type: violation_type.to_string(),
            reason: reason.to_string(),
            timestamp: Utc::now(),
            current_usage: usage.clone(),
            limits: RateLimitInfo {
                tool_limit: self.config.tool_limits.get(tool_name).cloned(),
                tenant_limit: self.config.tenant_limits.get(tenant_id).cloned(),
                global_limit: self.config.global_limits.clone(),
            },
        };

        let mut violations = self.violation_log.write().await;
        violations.push(violation);

        let n = violations.len();
        if n > 1000 {
            violations.drain(0..n - 1000);
        }

        info!(
            "Rate limit violation logged: tenant={}, tool={}, type={}, reason={}",
            tenant_id, tool_name, violation_type, reason
        );

        Ok(())
    }

    /// Get violation statistics
    pub async fn get_violation_stats(&self) -> Result<HashMap<String, u32>> {
        let violations = self.violation_log.read().await;
        let mut stats = HashMap::new();

        for violation in violations.iter() {
            *stats.entry(violation.violation_type.clone()).or_insert(0) += 1;
        }

        Ok(stats)
    }

    /// Update rate limit configuration
    pub async fn update_config(&mut self, new_config: RateLimitConfig) -> Result<()> {
        self.config = new_config;
        info!("Rate limit configuration updated");
        Ok(())
    }

    pub fn config(&self) -> &RateLimitConfig {
        &self.config
    }
}

impl UsageTracker {
    fn new() -> Self {
        Self {
            tool_usage: HashMap::new(),
            tenant_usage: HashMap::new(),
            global_usage: VecDeque::new(),
            budget_usage: HashMap::new(),
        }
    }

    fn window_cutoff(now: Instant, window: Duration) -> Option<Instant> {
        // Windows Instant can overflow when subtracting large durations from a
        // short-lived process clock; treat that as "no cutoff" (keep all).
        now.checked_sub(window)
    }

    fn get_requests_in_window(&self, timestamps: &VecDeque<Instant>, window: Duration) -> u32 {
        let now = Instant::now();
        let Some(cutoff) = Self::window_cutoff(now, window) else {
            return timestamps.len() as u32;
        };

        timestamps.iter().filter(|&ts| *ts > cutoff).count() as u32
    }

    fn get_budget_in_window(&self, events: &VecDeque<BudgetEvent>, window: Duration) -> f64 {
        let now = Instant::now();
        let Some(cutoff) = Self::window_cutoff(now, window) else {
            return events.iter().map(|e| e.amount).sum();
        };

        events
            .iter()
            .filter(|e| e.at > cutoff)
            .map(|e| e.amount)
            .sum()
    }

    fn cleanup_old_entries(&mut self) {
        let now = Instant::now();
        let Some(cutoff) = Self::window_cutoff(now, Duration::from_secs(86400)) else {
            return;
        };

        for tool_usage in self.tool_usage.values_mut() {
            for tenant_usage in tool_usage.values_mut() {
                while tenant_usage.front().is_some_and(|ts| *ts <= cutoff) {
                    tenant_usage.pop_front();
                }
            }
        }

        for tenant_usage in self.tenant_usage.values_mut() {
            while tenant_usage.front().is_some_and(|ts| *ts <= cutoff) {
                tenant_usage.pop_front();
            }
        }

        while self.global_usage.front().is_some_and(|ts| *ts <= cutoff) {
            self.global_usage.pop_front();
        }

        for events in self.budget_usage.values_mut() {
            while events.front().is_some_and(|e| e.at <= cutoff) {
                events.pop_front();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_rate_limiter_creation() {
        let config = RateLimitConfig::default();
        let limiter = RateLimiter::new(config);

        assert!(limiter.usage_tracker.read().await.tool_usage.is_empty());
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
    async fn test_violation_logging() {
        let config = RateLimitConfig::default();
        let limiter = RateLimiter::new(config);

        limiter
            .log_violation(
                "tenant1",
                "data_query",
                "RATE_LIMIT_EXCEEDED",
                "Too many requests",
                &RateLimitUsage {
                    requests_last_minute: 150,
                    requests_last_hour: 1000,
                    requests_last_day: 50000,
                    budget_consumed_last_minute: 0.0,
                    budget_consumed_last_hour: 0.0,
                    budget_consumed_last_day: 0.0,
                },
            )
            .await
            .unwrap();

        let stats = limiter.get_violation_stats().await.unwrap();
        assert_eq!(stats.get("RATE_LIMIT_EXCEEDED"), Some(&1));
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

        // 5.0 + 5.0 = 10.0 reaches budget_per_minute → next Deny
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

        let usage = limiter
            .get_current_usage("budget-tenant", "pricey")
            .await
            .unwrap();
        assert!((usage.budget_consumed_last_minute - 10.0).abs() < f64::EPSILON);

        let denied = limiter
            .check_rate_limit("budget-tenant", "pricey", "s1")
            .await
            .unwrap();
        assert!(
            matches!(denied, RateLimitDecision::Deny(ref r) if r.contains("budget exceeded")),
            "expected budget Deny, got {:?}",
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

        let a_denied = limiter
            .check_rate_limit("tenant-a", "shared", "s")
            .await
            .unwrap();
        assert!(matches!(a_denied, RateLimitDecision::Deny(_)));

        // Tenant B still has its own budget/window.
        let b_ok = limiter
            .check_rate_limit("tenant-b", "shared", "s")
            .await
            .unwrap();
        assert!(matches!(
            b_ok,
            RateLimitDecision::Allow | RateLimitDecision::Throttle(_)
        ));

        let usage_a = limiter.get_current_usage("tenant-a", "shared").await.unwrap();
        let usage_b = limiter.get_current_usage("tenant-b", "shared").await.unwrap();
        assert!(usage_a.requests_last_minute >= 3);
        assert_eq!(usage_b.requests_last_minute, 1);
    }

    #[tokio::test]
    async fn test_throttle_decision_emitted() {
        let mut config = RateLimitConfig::default();
        config.throttle_delay_ms = 25;
        config.tool_limits.insert(
            "soft".to_string(),
            ToolRateLimit {
                tool_name: "soft".to_string(),
                requests_per_minute: 2,
                requests_per_hour: 100,
                requests_per_day: 1000,
                burst_multiplier: 3.0, // burst=6 → soft exceed yields Throttle
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
        assert!(matches!(
            limiter.check_rate_limit("t", "soft", "s").await.unwrap(),
            RateLimitDecision::Allow
        ));

        let throttled = limiter.check_rate_limit("t", "soft", "s").await.unwrap();
        match throttled {
            RateLimitDecision::Throttle(ms) => assert!(ms >= 25),
            other => panic!("expected Throttle, got {:?}", other),
        }
    }
}
