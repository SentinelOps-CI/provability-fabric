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

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::error::Error;
use std::fs;
use std::path::Path;

/// DFA table structure matching Lean export
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DFATable {
    pub states: Vec<u32>,
    pub start: u32,
    pub accepting: Vec<u32>,
    pub transitions: Vec<Transition>,
    pub rate_limits: Vec<RateLimit>,
}

/// Transition: (from_state, event, to_state)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transition {
    pub from_state: u32,
    pub event: String,
    pub to_state: u32,
}

/// Rate limit: (tool, window_ms, bound)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimit {
    pub tool: String,
    pub window_ms: u32,
    pub bound: u32,
}

/// DFA interpreter state
#[derive(Debug, Clone)]
pub struct DFAInterpreter {
    table: DFATable,
    current_state: u32,
    transition_map: HashMap<(u32, String), u32>,
    rate_limiters: HashMap<String, RateLimiter>,
}

/// Rate limiter with sliding window
#[derive(Debug, Clone)]
struct RateLimiter {
    window_ms: u32,
    bound: u32,
    events: Vec<(u64, String)>, // (timestamp, event_hash)
}

impl RateLimiter {
    fn new(window_ms: u32, bound: u32) -> Self {
        Self {
            window_ms,
            bound,
            events: Vec::new(),
        }
    }

    fn check(&self, current_time: u64, event_hash: &str) -> bool {
        let window_start = if current_time >= self.window_ms as u64 {
            current_time - self.window_ms as u64
        } else {
            0
        };

        let relevant_events = self
            .events
            .iter()
            .filter(|(t, _)| *t >= window_start)
            .count();

        relevant_events < self.bound as usize
    }

    fn update(&mut self, current_time: u64, event_hash: String) {
        self.events.push((current_time, event_hash));

        // Clean old events outside window
        let window_start = if current_time >= self.window_ms as u64 {
            current_time - self.window_ms as u64
        } else {
            0
        };

        self.events.retain(|(t, _)| *t >= window_start);
    }
}

impl DFAInterpreter {
    /// Load DFA table from JSON file
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let content = fs::read_to_string(path)?;
        let table: DFATable = serde_json::from_str(&content)?;
        Ok(Self::from_table(table))
    }

    /// Create interpreter from DFA table
    pub fn from_table(table: DFATable) -> Self {
        let mut transition_map = HashMap::new();

        // Build transition lookup map
        for transition in &table.transitions {
            transition_map.insert(
                (transition.from_state, transition.event.clone()),
                transition.to_state,
            );
        }

        // Initialize rate limiters
        let mut rate_limiters = HashMap::new();
        for rate_limit in &table.rate_limits {
            rate_limiters.insert(
                rate_limit.tool.clone(),
                RateLimiter::new(rate_limit.window_ms, rate_limit.bound),
            );
        }

        Self {
            table,
            current_state: 0,
            transition_map,
            rate_limiters,
        }
    }

    /// Reset interpreter to start state
    pub fn reset(&mut self) {
        self.current_state = self.table.start;
    }

    /// Check if current state is accepting
    pub fn is_accepting(&self) -> bool {
        self.table.accepting.contains(&self.current_state)
    }

    /// Process an event and transition
    pub fn process_event(&mut self, event: &str, current_time: u64) -> Result<bool, String> {
        // Check rate limits first
        if !self.check_rate_limits(event, current_time) {
            return Err("Rate limit exceeded".to_string());
        }

        // Find transition
        let key = (self.current_state, event.to_string());
        let next_state = self.transition_map.get(&key).ok_or_else(|| {
            format!(
                "No transition for state {} with event {}",
                self.current_state, event
            )
        })?;

        // Update rate limiters
        self.update_rate_limits(event, current_time);

        // Transition to next state
        self.current_state = *next_state;
        Ok(true)
    }

    /// Check all applicable rate limits
    fn check_rate_limits(&self, event: &str, current_time: u64) -> bool {
        for (tool, limiter) in &self.rate_limiters {
            if event.contains(tool) {
                if !limiter.check(current_time, event) {
                    return false;
                }
            }
        }
        true
    }

    /// Update all applicable rate limiters
    fn update_rate_limits(&mut self, event: &str, current_time: u64) {
        for (tool, limiter) in &mut self.rate_limiters {
            if event.contains(tool) {
                limiter.update(current_time, event.to_string());
            }
        }
    }

    /// Get current state
    pub fn current_state(&self) -> u32 {
        self.current_state
    }

    /// Validate DFA table integrity
    pub fn validate(&self) -> Result<(), String> {
        // Check that start state exists
        if !self.table.states.contains(&self.table.start) {
            return Err("Start state not in states list".to_string());
        }

        // Check that all accepting states exist
        for &accepting_state in &self.table.accepting {
            if !self.table.states.contains(&accepting_state) {
                return Err(format!(
                    "Accepting state {} not in states list",
                    accepting_state
                ));
            }
        }

        // Check that all transition states exist
        for transition in &self.table.transitions {
            if !self.table.states.contains(&transition.from_state) {
                return Err(format!(
                    "From state {} not in states list",
                    transition.from_state
                ));
            }
            if !self.table.states.contains(&transition.to_state) {
                return Err(format!(
                    "To state {} not in states list",
                    transition.to_state
                ));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;

    #[test]
    fn test_dfa_loading() {
        let table = DFATable {
            states: vec![0, 1, 2],
            start: 0,
            accepting: vec![0, 1, 2],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,hash1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "log(hash2)".to_string(),
                    to_state: 2,
                },
                Transition {
                    from_state: 2,
                    event: "emit(plan1)".to_string(),
                    to_state: 0,
                },
            ],
            rate_limits: vec![
                RateLimit {
                    tool: "tool1".to_string(),
                    window_ms: 1000,
                    bound: 10,
                },
                RateLimit {
                    tool: "egress".to_string(),
                    window_ms: 5000,
                    bound: 1024,
                },
            ],
        };

        let interpreter = DFAInterpreter::from_table(table);
        assert_eq!(interpreter.current_state(), 0);
        assert!(interpreter.is_accepting());
    }

    #[test]
    fn test_dfa_transitions() {
        let table = DFATable {
            states: vec![0, 1, 2],
            start: 0,
            accepting: vec![0, 1, 2],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,hash1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "log(hash2)".to_string(),
                    to_state: 2,
                },
            ],
            rate_limits: vec![],
        };

        let mut interpreter = DFAInterpreter::from_table(table);

        // Process first event
        let result = interpreter.process_event("call(tool1,hash1)", 1000);
        assert!(result.is_ok());
        assert_eq!(interpreter.current_state(), 1);
        assert!(interpreter.is_accepting());

        // Process second event
        let result = interpreter.process_event("log(hash2)", 2000);
        assert!(result.is_ok());
        assert_eq!(interpreter.current_state(), 2);
        assert!(interpreter.is_accepting());
    }

    #[test]
    fn test_rate_limiting() {
        let table = DFATable {
            states: vec![0, 1],
            start: 0,
            accepting: vec![0, 1],
            transitions: vec![Transition {
                from_state: 0,
                event: "call(tool1,hash1)".to_string(),
                to_state: 1,
            }],
            rate_limits: vec![RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 2,
            }],
        };

        let mut interpreter = DFAInterpreter::from_table(table);

        // First call should succeed
        let result = interpreter.process_event("call(tool1,hash1)", 1000);
        assert!(result.is_ok());

        // Second call should succeed
        let result = interpreter.process_event("call(tool1,hash2)", 1500);
        assert!(result.is_ok());

        // Third call should fail (rate limit exceeded)
        let result = interpreter.process_event("call(tool1,hash3)", 2000);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Rate limit exceeded");
    }

    #[test]
    fn test_dfa_validation() {
        let invalid_table = DFATable {
            states: vec![0, 1],
            start: 2, // Invalid start state
            accepting: vec![0, 1],
            transitions: vec![],
            rate_limits: vec![],
        };

        let interpreter = DFAInterpreter::from_table(invalid_table);
        let validation = interpreter.validate();
        assert!(validation.is_err());
        assert_eq!(validation.unwrap_err(), "Start state not in states list");
    }
}
