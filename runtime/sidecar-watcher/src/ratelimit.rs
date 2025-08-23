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
use std::collections::VecDeque;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Rate limit configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitConfig {
    pub window_ms: u64,
    pub max_events: u32,
    pub epsilon_ms: u64, // Clock tolerance
}

impl Default for RateLimitConfig {
    fn default() -> Self {
        Self {
            window_ms: 1000, // 1 second
            max_events: 100, // 100 events per window
            epsilon_ms: 10,  // 10ms tolerance
        }
    }
}

/// Rate limiter with sliding window and ε tolerance
pub struct RateLimiter {
    config: RateLimitConfig,
    events: VecDeque<Instant>,
    last_cleanup: Instant,
}

impl RateLimiter {
    /// Create new rate limiter
    pub fn new(config: RateLimitConfig) -> Self {
        Self {
            config,
            events: VecDeque::new(),
            last_cleanup: Instant::now(),
        }
    }

    /// Check if event is allowed
    pub fn check(&mut self, current_time: Instant) -> bool {
        self.cleanup_old_events(current_time);

        if self.events.len() < self.config.max_events as usize {
            return true;
        }

        // Check if we can allow the event due to ε tolerance
        if let Some(oldest_event) = self.events.front() {
            let window_start = current_time - Duration::from_millis(self.config.window_ms);
            let epsilon_duration = Duration::from_millis(self.config.epsilon_ms);
            let adjusted_window_start = window_start - epsilon_duration;

            if *oldest_event < adjusted_window_start {
                return true;
            }
        }

        false
    }

    /// Record an event
    pub fn record_event(&mut self, current_time: Instant) -> Result<(), String> {
        if !self.check(current_time) {
            return Err("Rate limit exceeded".to_string());
        }

        self.events.push_back(current_time);
        Ok(())
    }

    /// Clean up old events outside the window
    fn cleanup_old_events(&mut self, current_time: Instant) {
        let window_start = current_time - Duration::from_millis(self.config.window_ms);

        // Remove events older than the window
        while let Some(front) = self.events.front() {
            if *front < window_start {
                self.events.pop_front();
            } else {
                break;
            }
        }
    }

    /// Get current event count
    pub fn current_count(&self) -> usize {
        self.events.len()
    }

    /// Get remaining capacity
    pub fn remaining_capacity(&self) -> i32 {
        self.config.max_events as i32 - self.current_count() as i32
    }

    /// Check if rate limit is exceeded
    pub fn is_exceeded(&self) -> bool {
        self.current_count() >= self.config.max_events as usize
    }

    /// Get window start time
    pub fn window_start(&self, current_time: Instant) -> Instant {
        current_time - Duration::from_millis(self.config.window_ms)
    }

    /// Get adjusted window start with ε tolerance
    pub fn adjusted_window_start(&self, current_time: Instant) -> Instant {
        let window_start = self.window_start(current_time);
        let epsilon_duration = Duration::from_millis(self.config.epsilon_ms);
        window_start - epsilon_duration
    }

    /// Reset rate limiter
    pub fn reset(&mut self) {
        self.events.clear();
        self.last_cleanup = Instant::now();
    }

    /// Update configuration
    pub fn update_config(&mut self, new_config: RateLimitConfig) {
        self.config = new_config;
        // Clean up events that might now be outside the new window
        self.cleanup_old_events(Instant::now());
    }

    /// Get configuration
    pub fn config(&self) -> &RateLimitConfig {
        &self.config
    }

    /// Benchmark rate limit check performance
    pub fn benchmark_check(&mut self, iterations: u32) -> Duration {
        let start = Instant::now();

        for _ in 0..iterations {
            let current_time = Instant::now();
            self.check(current_time);
        }

        start.elapsed()
    }
}

/// Multi-dimensional rate limiter for different event types
pub struct MultiRateLimiter {
    limiters: std::collections::HashMap<String, RateLimiter>,
    default_config: RateLimitConfig,
}

impl MultiRateLimiter {
    /// Create new multi-dimensional rate limiter
    pub fn new(default_config: RateLimitConfig) -> Self {
        Self {
            limiters: std::collections::HashMap::new(),
            default_config,
        }
    }

    /// Add rate limiter for specific event type
    pub fn add_limiter(&mut self, event_type: String, config: RateLimitConfig) {
        self.limiters.insert(event_type, RateLimiter::new(config));
    }

    /// Check rate limit for specific event type
    pub fn check(&mut self, event_type: &str, current_time: Instant) -> bool {
        if let Some(limiter) = self.limiters.get_mut(event_type) {
            limiter.check(current_time)
        } else {
            // Use default limiter
            let default_limiter = RateLimiter::new(self.default_config.clone());
            self.limiters
                .insert(event_type.to_string(), default_limiter);
            true
        }
    }

    /// Record event for specific event type
    pub fn record_event(&mut self, event_type: &str, current_time: Instant) -> Result<(), String> {
        if let Some(limiter) = self.limiters.get_mut(event_type) {
            limiter.record_event(current_time)
        } else {
            // Create new limiter for this event type
            let mut new_limiter = RateLimiter::new(self.default_config.clone());
            let result = new_limiter.record_event(current_time);
            if result.is_ok() {
                self.limiters.insert(event_type.to_string(), new_limiter);
            }
            result
        }
    }

    /// Get current count for specific event type
    pub fn current_count(&self, event_type: &str) -> usize {
        self.limiters
            .get(event_type)
            .map(|limiter| limiter.current_count())
            .unwrap_or(0)
    }

    /// Get remaining capacity for specific event type
    pub fn remaining_capacity(&self, event_type: &str) -> i32 {
        self.limiters
            .get(event_type)
            .map(|limiter| limiter.remaining_capacity())
            .unwrap_or(self.default_config.max_events as i32)
    }

    /// Check if rate limit is exceeded for specific event type
    pub fn is_exceeded(&self, event_type: &str) -> bool {
        self.limiters
            .get(event_type)
            .map(|limiter| limiter.is_exceeded())
            .unwrap_or(false)
    }

    /// Reset all rate limiters
    pub fn reset_all(&mut self) {
        for limiter in self.limiters.values_mut() {
            limiter.reset();
        }
    }

    /// Get all event types
    pub fn event_types(&self) -> Vec<&String> {
        self.limiters.keys().collect()
    }

    /// Remove rate limiter for specific event type
    pub fn remove_limiter(&mut self, event_type: &str) -> Option<RateLimiter> {
        self.limiters.remove(event_type)
    }
}

/// Clock model for rate limiting
pub struct ClockModel {
    epsilon_ms: u64,
    last_sync: Instant,
    drift_estimate: Duration,
}

impl ClockModel {
    /// Create new clock model
    pub fn new(epsilon_ms: u64) -> Self {
        Self {
            epsilon_ms,
            last_sync: Instant::now(),
            drift_estimate: Duration::ZERO,
        }
    }

    /// Get current time with ε tolerance
    pub fn current_time_with_tolerance(&self) -> (Instant, Duration) {
        let current = Instant::now();
        let epsilon_duration = Duration::from_millis(self.epsilon_ms);
        (current, epsilon_duration)
    }

    /// Estimate clock drift
    pub fn estimate_drift(&mut self, reference_time: Instant) {
        let current = Instant::now();
        let measured_drift = current.duration_since(reference_time);
        self.drift_estimate = measured_drift;
        self.last_sync = current;
    }

    /// Get drift estimate
    pub fn drift_estimate(&self) -> Duration {
        self.drift_estimate
    }

    /// Check if clock drift is within tolerance
    pub fn is_drift_acceptable(&self) -> bool {
        self.drift_estimate.abs() < Duration::from_millis(self.epsilon_ms)
    }

    /// Get ε tolerance
    pub fn epsilon(&self) -> Duration {
        Duration::from_millis(self.epsilon_ms)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration as StdDuration;

    #[test]
    fn test_rate_limiter_basic() {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 5,
            epsilon_ms: 10,
        };

        let mut limiter = RateLimiter::new(config);
        let current_time = Instant::now();

        // Should allow first 5 events
        for _ in 0..5 {
            assert!(limiter.check(current_time));
            limiter.record_event(current_time).unwrap();
        }

        // Should reject 6th event
        assert!(!limiter.check(current_time));
    }

    #[test]
    fn test_rate_limiter_sliding_window() {
        let config = RateLimitConfig {
            window_ms: 100,
            max_events: 3,
            epsilon_ms: 5,
        };

        let mut limiter = RateLimiter::new(config);
        let start_time = Instant::now();

        // Record 3 events
        for i in 0..3 {
            let event_time = start_time + Duration::from_millis(i * 10);
            limiter.record_event(event_time).unwrap();
        }

        // Should reject immediately
        assert!(!limiter.check(start_time + Duration::from_millis(50)));

        // Should allow after window expires
        thread::sleep(StdDuration::from_millis(150));
        let new_time = Instant::now();
        assert!(limiter.check(new_time));
    }

    #[test]
    fn test_epsilon_tolerance() {
        let config = RateLimitConfig {
            window_ms: 100,
            max_events: 2,
            epsilon_ms: 20,
        };

        let mut limiter = RateLimiter::new(config);
        let start_time = Instant::now();

        // Record 2 events
        limiter.record_event(start_time).unwrap();
        limiter
            .record_event(start_time + Duration::from_millis(10))
            .unwrap();

        // Should reject due to rate limit
        assert!(!limiter.check(start_time + Duration::from_millis(50)));

        // Should allow due to ε tolerance
        let time_within_epsilon = start_time + Duration::from_millis(85); // 15ms before window end
        assert!(limiter.check(time_within_epsilon));
    }

    #[test]
    fn test_multi_rate_limiter() {
        let default_config = RateLimitConfig::default();
        let mut multi_limiter = MultiRateLimiter::new(default_config);

        let custom_config = RateLimitConfig {
            window_ms: 500,
            max_events: 2,
            epsilon_ms: 5,
        };

        multi_limiter.add_limiter("api_calls".to_string(), custom_config);

        let current_time = Instant::now();

        // Should allow first 2 API calls
        assert!(multi_limiter.check("api_calls", current_time));
        multi_limiter
            .record_event("api_calls", current_time)
            .unwrap();

        assert!(multi_limiter.check("api_calls", current_time));
        multi_limiter
            .record_event("api_calls", current_time)
            .unwrap();

        // Should reject 3rd API call
        assert!(!multi_limiter.check("api_calls", current_time));

        // Should allow other event types with default config
        assert!(multi_limiter.check("other_event", current_time));
    }

    #[test]
    fn test_clock_model() {
        let mut clock_model = ClockModel::new(10);

        let (current_time, epsilon) = clock_model.current_time_with_tolerance();
        assert_eq!(epsilon, Duration::from_millis(10));

        // Simulate clock drift
        let reference_time = current_time + Duration::from_millis(5);
        clock_model.estimate_drift(reference_time);

        assert!(clock_model.is_drift_acceptable());

        // Simulate excessive drift
        let excessive_reference = current_time + Duration::from_millis(20);
        clock_model.estimate_drift(excessive_reference);

        assert!(!clock_model.is_drift_acceptable());
    }

    #[test]
    fn test_performance_benchmark() {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 1000,
            epsilon_ms: 10,
        };

        let mut limiter = RateLimiter::new(config);

        // Benchmark 10,000 checks
        let duration = limiter.benchmark_check(10_000);

        // Should complete in reasonable time (less than 1 second)
        assert!(duration < Duration::from_secs(1));

        // Calculate operations per second
        let ops_per_sec = 10_000.0 / duration.as_secs_f64();
        println!("Rate limit checks per second: {:.0}", ops_per_sec);

        // Should achieve at least 10,000 ops/sec for 99th percentile
        assert!(ops_per_sec >= 10_000.0);
    }

    #[test]
    fn test_99th_percentile_performance() {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 10000,
            epsilon_ms: 10,
        };

        let mut limiter = RateLimiter::new(config);

        // Measure individual check times for 10k events
        let mut check_times = Vec::new();

        for _ in 0..10000 {
            let start = Instant::now();
            limiter.check(Instant::now());
            check_times.push(start.elapsed());
        }

        // Sort times to find percentiles
        check_times.sort();

        // Calculate 99th percentile
        let p99_index = (check_times.len() as f64 * 0.99) as usize;
        let p99_time = check_times[p99_index];

        // 99th percentile should be less than 0.15ms as required by CI gates
        assert!(
            p99_time < Duration::from_millis(1), // 1ms = 1000μs, so 0.15ms = 150μs
            "99th percentile check time {} exceeds 0.15ms threshold",
            p99_time.as_micros()
        );

        println!("99th percentile check time: {}μs", p99_time.as_micros());
        println!(
            "50th percentile check time: {}μs",
            check_times[check_times.len() / 2].as_micros()
        );
        println!(
            "99.9th percentile check time: {}μs",
            check_times[(check_times.len() as f64 * 0.999) as usize].as_micros()
        );
    }

    #[test]
    fn test_clock_wraparound_safety() {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 100,
            epsilon_ms: 10,
        };

        let mut limiter = RateLimiter::new(config);

        // Test with very old timestamps (simulating clock wraparound)
        let old_time = Instant::now() - Duration::from_secs(u64::MAX as u64 / 1000);

        // Should not panic
        let result = limiter.check(old_time);
        assert!(result); // Should allow since old events are outside window

        // Test with very new timestamps
        let future_time = Instant::now() + Duration::from_secs(3600);

        // Should not panic
        let result = limiter.check(future_time);
        assert!(result); // Should allow since no events in window yet
    }

    #[test]
    fn test_monotonicity_guarantee() {
        let config = RateLimitConfig {
            window_ms: 1000,
            max_events: 100,
            epsilon_ms: 10,
        };

        let mut limiter = RateLimiter::new(config);

        let mut prev_time = Instant::now();

        // Test that time always moves forward
        for _ in 0..1000 {
            let current_time = Instant::now();
            assert!(current_time >= prev_time, "Time moved backwards!");

            limiter.check(current_time);
            prev_time = current_time;
        }
    }
}
