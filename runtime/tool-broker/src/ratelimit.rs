// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn, error};
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
        
        // Default limits for common tools
        tool_limits.insert("data_query".to_string(), ToolRateLimit {
            tool_name: "data_query".to_string(),
            requests_per_minute: 100,
            requests_per_hour: 5000,
            requests_per_day: 100000,
            burst_multiplier: 2.0,
            requires_approval_above: 50,
        });
        
        tool_limits.insert("retrieval".to_string(), ToolRateLimit {
            tool_name: "retrieval".to_string(),
            requests_per_minute: 200,
            requests_per_hour: 10000,
            requests_per_day: 200000,
            burst_multiplier: 1.5,
            requires_approval_above: 100,
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
            sliding_window_ms: 60000, // 1 minute sliding window
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
    usage_tracker: Arc<RwLock<UsageTracker>>,
    violation_log: Arc<RwLock<Vec<RateLimitViolation>>>,
}

/// Tracks usage across different time windows
struct UsageTracker {
    tool_usage: HashMap<String, HashMap<String, VecDeque<Instant>>>, // tool -> tenant -> timestamps
    tenant_usage: HashMap<String, VecDeque<Instant>>, // tenant -> timestamps
    global_usage: VecDeque<Instant>,
    budget_usage: HashMap<String, HashMap<String, f64>>, // tenant -> time_window -> amount
}

impl RateLimiter {
    pub fn new(config: RateLimitConfig) -> Self {
        Self {
            config,
            usage_tracker: Arc::new(RwLock::new(UsageTracker::new())),
            violation_log: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// Check if a request is allowed based on rate limits
    pub async fn check_rate_limit(
        &self,
        tenant_id: &str,
        tool_name: &str,
        session_id: &str,
    ) -> Result<RateLimitDecision> {
        let start_time = Instant::now();
        
        // Get current usage
        let usage = self.get_current_usage(tenant_id, tool_name).await?;
        
        // Check global limits first
        if let RateLimitDecision::Deny(reason) = self.check_global_limits(&usage).await? {
            return Ok(RateLimitDecision::Deny(reason));
        }
        
        // Check tenant limits
        if let RateLimitDecision::Deny(reason) = self.check_tenant_limits(tenant_id, &usage).await? {
            return Ok(RateLimitDecision::Deny(reason));
        }
        
        // Check tool-specific limits
        if let RateLimitDecision::Deny(reason) = self.check_tool_limits(tool_name, tenant_id, &usage).await? {
            return Ok(RateLimitDecision::Deny(reason));
        }
        
        // Check if approval is required
        if let Some(approval_reason) = self.check_approval_required(tool_name, tenant_id, &usage).await? {
            return Ok(RateLimitDecision::RequireApproval(approval_reason));
        }
        
        // Update usage tracker
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
        let tracker = self.usage_tracker.read().await;
        
        if usage.requests_last_minute > self.config.global_limits.max_requests_per_minute {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for minute".to_string()
            ));
        }
        
        if usage.requests_last_hour > self.config.global_limits.max_requests_per_hour {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for hour".to_string()
            ));
        }
        
        if usage.requests_last_day > self.config.global_limits.max_requests_per_day {
            return Ok(RateLimitDecision::Deny(
                "Global rate limit exceeded for day".to_string()
            ));
        }
        
        Ok(RateLimitDecision::Allow)
    }

    /// Check tenant-specific rate limits
    async fn check_tenant_limits(&self, tenant_id: &str, usage: &RateLimitUsage) -> Result<RateLimitDecision> {
        if let Some(tenant_limit) = self.config.tenant_limits.get(tenant_id) {
            if usage.requests_last_minute > tenant_limit.total_requests_per_minute {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for minute: {}", tenant_id)
                ));
            }
            
            if usage.requests_last_hour > tenant_limit.total_requests_per_hour {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for hour: {}", tenant_id)
                ));
            }
            
            if usage.requests_last_day > tenant_limit.total_requests_per_day {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant rate limit exceeded for day: {}", tenant_id)
                ));
            }
            
            // Check budget limits
            if usage.budget_consumed_last_minute > tenant_limit.budget_per_minute {
                return Ok(RateLimitDecision::Deny(
                    format!("Tenant budget exceeded for minute: {}", tenant_id)
                ));
            }
        }
        
        Ok(RateLimitDecision::Allow)
    }

    /// Check tool-specific rate limits
    async fn check_tool_limits(
        &self,
        tool_name: &str,
        tenant_id: &str,
        usage: &RateLimitUsage,
    ) -> Result<RateLimitDecision> {
        if let Some(tool_limit) = self.config.tool_limits.get(tool_name) {
            // Check if current usage exceeds burst allowance
            let burst_limit = (tool_limit.requests_per_minute as f64 * tool_limit.burst_multiplier) as u32;
            
            if usage.requests_last_minute > burst_limit {
                return Ok(RateLimitDecision::Deny(
                    format!("Tool burst limit exceeded: {} > {}", usage.requests_last_minute, burst_limit)
                ));
            }
        }
        
        Ok(RateLimitDecision::Allow)
    }

    /// Check if approval is required based on usage patterns
    async fn check_approval_required(
        &self,
        tool_name: &str,
        tenant_id: &str,
        usage: &RateLimitUsage,
    ) -> Result<Option<String>> {
        if let Some(tool_limit) = self.config.tool_limits.get(tool_name) {
            if usage.requests_last_minute > tool_limit.requires_approval_above {
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

    /// Get current usage statistics
    async fn get_current_usage(&self, tenant_id: &str, tool_name: &str) -> Result<RateLimitUsage> {
        let tracker = self.usage_tracker.read().await;
        let now = Instant::now();
        
        let requests_last_minute = tracker.get_requests_in_window(
            &tracker.tool_usage.get(tool_name)
                .and_then(|t| t.get(tenant_id))
                .cloned()
                .unwrap_or_default(),
            Duration::from_secs(60)
        );
        
        let requests_last_hour = tracker.get_requests_in_window(
            &tracker.tool_usage.get(tool_name)
                .and_then(|t| t.get(tenant_id))
                .cloned()
                .unwrap_or_default(),
            Duration::from_secs(3600)
        );
        
        let requests_last_day = tracker.get_requests_in_window(
            &tracker.tool_usage.get(tool_name)
                .and_then(|t| t.get(tenant_id))
                .cloned()
                .unwrap_or_default(),
            Duration::from_secs(86400)
        );
        
        Ok(RateLimitUsage {
            requests_last_minute,
            requests_last_hour,
            requests_last_day,
            budget_consumed_last_minute: 0.0, // TODO: Implement budget tracking
            budget_consumed_last_hour: 0.0,
            budget_consumed_last_day: 0.0,
        })
    }

    /// Record usage for rate limiting
    async fn record_usage(&self, tenant_id: &str, tool_name: &str) -> Result<()> {
        let mut tracker = self.usage_tracker.write().await;
        let now = Instant::now();
        
        // Record tool usage
        tracker.tool_usage
            .entry(tool_name.to_string())
            .or_default()
            .entry(tenant_id.to_string())
            .or_default()
            .push_back(now);
        
        // Record tenant usage
        tracker.tenant_usage
            .entry(tenant_id.to_string())
            .or_default()
            .push_back(now);
        
        // Record global usage
        tracker.global_usage.push_back(now);
        
        // Clean up old entries
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
        
        // Keep only last 1000 violations
        if violations.len() > 1000 {
            violations.drain(0..violations.len() - 1000);
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
    
    fn get_requests_in_window(&self, timestamps: &VecDeque<Instant>, window: Duration) -> u32 {
        let now = Instant::now();
        let cutoff = now - window;
        
        timestamps.iter()
            .filter(|&ts| *ts > cutoff)
            .count() as u32
    }
    
    fn cleanup_old_entries(&mut self) {
        let now = Instant::now();
        let cutoff = now - Duration::from_secs(86400); // 24 hours
        
        // Clean up tool usage
        for tool_usage in self.tool_usage.values_mut() {
            for tenant_usage in tool_usage.values_mut() {
                tenant_usage.retain(|&ts| ts > cutoff);
            }
        }
        
        // Clean up tenant usage
        for tenant_usage in self.tenant_usage.values_mut() {
            tenant_usage.retain(|&ts| ts > cutoff);
        }
        
        // Clean up global usage
        self.global_usage.retain(|&ts| ts > cutoff);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    
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
    async fn test_violation_logging() {
        let config = RateLimitConfig::default();
        let limiter = RateLimiter::new(config);
        
        limiter.log_violation(
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
            }
        ).await.unwrap();
        
        let stats = limiter.get_violation_stats().await.unwrap();
        assert_eq!(stats.get("RATE_LIMIT_EXCEEDED"), Some(&1));
    }
}
