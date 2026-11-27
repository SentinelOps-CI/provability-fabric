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
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs;
use std::path::Path;

/// Event kind for fast dispatch
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(u8)]
pub enum EventKind {
    Call = 0,
    Emit = 1,
    Log = 2,
    Declassify = 3,
    Retrieve = 4,
    DataQuery = 5,
    Search = 6,
    Fetch = 7,
    Get = 8,
    Compute = 9,
    Analyze = 10,
    Transform = 11,
    Aggregate = 12,
    Notify = 13,
    Alert = 14,
    Report = 15,
    Export = 16,
    Validate = 17,
    Verify = 18,
    Audit = 19,
    ComplianceCheck = 20,
}

impl EventKind {
    #[inline(always)]
    #[allow(clippy::should_implement_trait)]
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "call" => Some(EventKind::Call),
            "emit" => Some(EventKind::Emit),
            "log" => Some(EventKind::Log),
            "declassify" => Some(EventKind::Declassify),
            "retrieve" => Some(EventKind::Retrieve),
            "data_query" => Some(EventKind::DataQuery),
            "search" => Some(EventKind::Search),
            "fetch" => Some(EventKind::Fetch),
            "get" => Some(EventKind::Get),
            "compute" => Some(EventKind::Compute),
            "analyze" => Some(EventKind::Analyze),
            "transform" => Some(EventKind::Transform),
            "aggregate" => Some(EventKind::Aggregate),
            "notify" => Some(EventKind::Notify),
            "alert" => Some(EventKind::Alert),
            "report" => Some(EventKind::Report),
            "export" => Some(EventKind::Export),
            "validate" => Some(EventKind::Validate),
            "verify" => Some(EventKind::Verify),
            "audit" => Some(EventKind::Audit),
            "compliance_check" => Some(EventKind::ComplianceCheck),
            _ => None,
        }
    }
}

/// State ID type for efficient indexing
pub type StateId = u32;

/// Call tag for event classification
pub type CallTag = u16;

/// Emit bucket for event classification
pub type EmitBucket = u16;

/// Optimized DFA state structure with C layout for cache locality
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DFAState {
    pub id: StateId,
    pub is_accepting: bool,
    pub call_transitions: [StateId; 256], // Jump table for call events
    pub emit_transitions: [StateId; 256], // Jump table for emit events
    pub default_state: StateId,           // Fallback state
}

impl Default for DFAState {
    fn default() -> Self {
        Self {
            id: 0,
            is_accepting: false,
            call_transitions: [0; 256],
            emit_transitions: [0; 256],
            default_state: 0,
        }
    }
}

/// Exact-event DFA index. Lookup borrows the event string and preserves state IDs.
pub struct OptimizedDFA {
    states: HashSet<StateId>,
    start_state: StateId,
    current_state: StateId,
    accepting_states: HashSet<StateId>,
    transitions: Vec<(StateId, Vec<(String, StateId)>)>,
    rate_limiters: HashMap<String, LegacyRateLimiter>,
}

/// Event structure for hot path processing
#[derive(Debug, Clone)]
pub struct Event {
    pub kind: EventKind,
    pub call_tag: CallTag,
    pub emit_bucket: EmitBucket,
    pub tool_name: String,
    pub timestamp: u32,
}

impl Event {
    pub fn new(
        kind: EventKind,
        call_tag: CallTag,
        emit_bucket: EmitBucket,
        tool_name: String,
    ) -> Self {
        Self {
            kind,
            call_tag,
            emit_bucket,
            tool_name,
            timestamp: 0, // Will be set by caller
        }
    }
}

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
    rate_limiters: HashMap<String, LegacyRateLimiter>,
    validation_error: Option<String>,
}

impl OptimizedDFA {
    /// Index a validated policy without changing its language or state identity.
    pub fn from_table(table: DFATable) -> Result<Self, Box<dyn Error>> {
        DFAInterpreter::from_table(table.clone())
            .validate().map_err(std::io::Error::other)?;
        // Sorted sparse rows avoid repeated hashing while retaining exact
        // symbol equality and memory proportional to the policy size.
        let mut rows: std::collections::BTreeMap<StateId, Vec<(String, StateId)>> =
            std::collections::BTreeMap::new();
        for transition in table.transitions {
            rows.entry(transition.from_state).or_default()
                .push((transition.event, transition.to_state));
        }
        let transitions = rows.into_iter().map(|(state, mut edges)| {
            edges.sort_unstable_by(|a, b| a.0.cmp(&b.0));
            (state, edges)
        }).collect();
        let rate_limiters = table.rate_limits.into_iter().map(|limit| {
            (limit.tool, LegacyRateLimiter::new(limit.window_ms, limit.bound))
        }).collect();
        Ok(Self {
            states: table.states.into_iter().collect(),
            start_state: table.start,
            current_state: table.start,
            accepting_states: table.accepting.into_iter().collect(),
            transitions,
            rate_limiters,
        })
    }

    /// Borrowed exact-symbol lookup. None denotes a missing transition.
    #[inline]
    pub fn step(&self, state: StateId, event: &str) -> Option<StateId> {
        let rows = &self.transitions;
        let row = if rows.len() <= 8 {
            rows.iter().find(|(id, _)| *id == state)?
        } else {
            &rows[rows.binary_search_by_key(&state, |(id, _)| *id).ok()?]
        };
        let edges = &row.1;
        if edges.len() <= 8 {
            edges.iter().find(|(symbol, _)| symbol == event).map(|(_, to)| *to)
        } else {
            let index = edges.binary_search_by(|(symbol, _)| symbol.as_str().cmp(event)).ok()?;
            Some(edges[index].1)
        }
    }

    /// Rejected events change neither state nor rate-limit history.
    pub fn process_event(&mut self, event: &str, current_time_ms: u64) -> Result<bool, String> {
        if self.rate_limiters.iter().any(|(tool, limiter)| {
            event.contains(tool) && !limiter.check(current_time_ms, event)
        }) {
            return Err("Rate limit exceeded".to_string());
        }
        let next = self.step(self.current_state, event).ok_or_else(|| {
            format!("No transition for state {} with event {}", self.current_state, event)
        })?;
        for (tool, limiter) in &mut self.rate_limiters {
            if event.contains(tool) {
                limiter.update(current_time_ms, event.to_string());
            }
        }
        self.current_state = next;
        Ok(true)
    }

    pub fn current_state(&self) -> StateId {
        self.current_state
    }

    pub fn is_accepting(&self, state: StateId) -> bool {
        self.accepting_states.contains(&state)
    }

    /// Reset the automaton state, preserving rate-limit history.
    pub fn reset(&mut self) {
        self.current_state = self.start_state;
    }

    pub fn validate(&self) -> Result<(), String> {
        if !self.states.contains(&self.start_state)
            || !self.accepting_states.is_subset(&self.states)
            || self.transitions.iter().any(|(from, edges)| {
                !self.states.contains(from)
                    || edges.iter().any(|(_, to)| !self.states.contains(to))
            })
        {
            return Err("Invalid indexed DFA state".to_string());
        }
        Ok(())
    }
}

/// Legacy rate limiter with sliding window
#[derive(Debug, Clone)]
struct LegacyRateLimiter {
    window_ms: u32,
    bound: u32,
    events: Vec<(u64, String)>, // (timestamp, event_hash)
}

impl LegacyRateLimiter {
    fn new(window_ms: u32, bound: u32) -> Self {
        Self {
            window_ms,
            bound,
            events: Vec::new(),
        }
    }

    fn check(&self, current_time: u64, _event_hash: &str) -> bool {
        let window_start = current_time.saturating_sub(self.window_ms as u64);

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
        let window_start = current_time.saturating_sub(self.window_ms as u64);

        self.events.retain(|(t, _)| *t >= window_start);
    }
}

impl DFAInterpreter {
    /// Load DFA table from JSON file
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn Error>> {
        let content = fs::read_to_string(path)?;
        let table: DFATable = serde_json::from_str(&content)?;
        let interpreter = Self::from_table(table);
        interpreter.validate().map_err(std::io::Error::other)?;
        Ok(interpreter)
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
                LegacyRateLimiter::new(rate_limit.window_ms, rate_limit.bound),
            );
        }

        let mut interpreter = Self {
            current_state: table.start,
            table,
            transition_map,
            rate_limiters,
            validation_error: None,
        };
        interpreter.validation_error = interpreter.validate().err();
        interpreter
    }

    /// Reset interpreter to start state
    pub fn reset(&mut self) {
        self.current_state = self.table.start;
    }

    /// Check if current state is accepting
    pub fn is_accepting(&self) -> bool {
        self.validation_error.is_none() && self.table.accepting.contains(&self.current_state)
    }

    /// Process an event and transition
    pub fn process_event(&mut self, event: &str, current_time: u64) -> Result<bool, String> {
        if let Some(ref error) = self.validation_error {
            return Err(format!("Invalid DFA: {error}"));
        }
        // Check rate limits first
        if !self.check_rate_limits(event, current_time) {
            return Err("Rate limit exceeded".to_string());
        }

        // Find transition
        let key = (self.current_state, event.to_string());
        let next_state = *self.transition_map.get(&key).ok_or_else(|| {
            format!(
                "No transition for state {} with event {}",
                self.current_state, event
            )
        })?;

        // Update rate limiters
        self.update_rate_limits(event, current_time);

        // Transition to next state
        self.current_state = next_state;
        Ok(true)
    }

    /// Check all applicable rate limits
    fn check_rate_limits(&self, event: &str, current_time: u64) -> bool {
        for (tool, limiter) in &self.rate_limiters {
            if event.contains(tool)
                && !limiter.check(current_time, event) {
                    return false;
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

        let mut states = HashSet::new();
        for &state in &self.table.states {
            if !states.insert(state) {
                return Err(format!("Duplicate DFA state {state}"));
            }
        }

        // Reject ambiguous transitions before they can be silently overwritten.
        let mut transition_keys = HashSet::new();
        // Check that all transition states exist
        for transition in &self.table.transitions {
            if transition.event.is_empty() {
                return Err("Empty DFA event".to_string());
            }
            if !transition_keys.insert((transition.from_state, transition.event.as_str())) {
                return Err(format!(
                    "Duplicate transition from state {} for event {}",
                    transition.from_state, transition.event
                ));
            }
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

        let mut rate_limit_tools = HashSet::new();
        for limit in &self.table.rate_limits {
            if limit.tool.is_empty() || limit.window_ms == 0 {
                return Err("Invalid DFA rate-limit tool or window".to_string());
            }
            if !rate_limit_tools.insert(limit.tool.as_str()) {
                return Err(format!("Duplicate rate limit for tool {}", limit.tool));
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_optimized_dfa_creation() {
        let table = DFATable {
            states: vec![0, 1, 2],
            start: 0,
            accepting: vec![0, 1, 2],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "emit(plan1)".to_string(),
                    to_state: 2,
                },
            ],
            rate_limits: vec![RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 10,
            }],
        };

        let dfa = OptimizedDFA::from_table(table).unwrap();
        assert_eq!(dfa.current_state(), 0);
        assert!(dfa.is_accepting(0));
    }

    #[test]
    fn test_hot_path_step() {
        let table = DFATable {
            states: vec![0, 1, 2],
            start: 0,
            accepting: vec![0, 1, 2],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "emit(plan1)".to_string(),
                    to_state: 2,
                },
            ],
            rate_limits: vec![],
        };

        let dfa = OptimizedDFA::from_table(table).unwrap();

        assert_eq!(dfa.step(0, "call(tool1,1)"), Some(1));
        assert_eq!(dfa.step(0, "call(tool2,1)"), None);
        assert_eq!(dfa.step(0, "call(tool1,257)"), None);
        assert_eq!(dfa.step(1, "emit(plan1)"), Some(2));
        assert_eq!(dfa.step(1, "emit(plan2)"), None);
        assert_eq!(dfa.step(99, "call(tool1,1)"), None);
    }

    #[test]
    fn test_rate_limiting() {
        let table = DFATable {
            states: vec![0, 1],
            start: 0,
            accepting: vec![0, 1],
            transitions: vec![
                Transition { from_state: 0, event: "call(tool1,1)".into(), to_state: 1 },
                Transition { from_state: 1, event: "call(tool1,1)".into(), to_state: 1 },
            ],
            rate_limits: vec![RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 2,
            }],
        };

        let mut dfa = OptimizedDFA::from_table(table).unwrap();

        let event = "call(tool1,1)";
        assert!(dfa.process_event(event, 1000).is_ok());
        assert_eq!(dfa.current_state(), 1);
        assert!(dfa.process_event(event, 1500).is_ok());
        assert_eq!(dfa.process_event(event, 2000).unwrap_err(), "Rate limit exceeded");
        assert_eq!(dfa.current_state(), 1);
        assert!(dfa.process_event(event, 2001).is_ok());
    }

    #[test]
    fn test_sparse_sorted_rows_match_exact_reference() {
        // Exercise both sides of the small-row threshold and sparse IDs.
        let states: Vec<u32> = (0..20).map(|n| n * 1009).collect();
        let mut transitions = Vec::new();
        for (n, &state) in states.iter().enumerate() {
            for k in 0..(n % 13 + 1) {
                transitions.push(Transition {
                    from_state: state,
                    event: format!("event-{k:02}"),
                    to_state: states[(n+k+1) % states.len()],
                });
            }
        }
        transitions.reverse();
        let table = DFATable {
            states: states.clone(),
            start: states[0],
            accepting: states.clone(),
            transitions: transitions.clone(),
            rate_limits: vec![],
        };
        let dfa = OptimizedDFA::from_table(table).unwrap();
        for state in states.into_iter().chain([u32::MAX, 17]) {
            for event in (0..15).map(|k| format!("event-{k:02}")).chain(["event".into(), "EVENT-00".into()]) {
                let expected = transitions.iter().find(|t| t.from_state == state && t.event == event)
                    .map(|t| t.to_state);
                assert_eq!(dfa.step(state, &event), expected);
            }
        }
    }

    #[test]
    fn test_performance_benchmark() {
        let table = DFATable {
            states: vec![0, 1, 2, 3, 4, 5],
            start: 0,
            accepting: vec![0, 1, 2, 3, 4, 5],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "emit(plan1)".to_string(),
                    to_state: 2,
                },
                Transition {
                    from_state: 2,
                    event: "log(hash1)".to_string(),
                    to_state: 3,
                },
            ],
            rate_limits: vec![],
        };

        let dfa = OptimizedDFA::from_table(table).unwrap();

        let event = "call(tool1,1)";
        assert_eq!(dfa.step(0, event), Some(1));
        let start = Instant::now();
        for _ in 0..100_000 {
            std::hint::black_box(dfa.step(std::hint::black_box(0), std::hint::black_box(event)));
        }
        let duration = start.elapsed();

        // The candidate workflow executes this threshold in optimized builds.
        if !cfg!(debug_assertions) {
            assert!(duration.as_millis() < 1, "Hot path too slow: {:?}", duration);
        }
        println!("100k hot path operations took: {:?}", duration);
    }

    #[test]
    fn test_legacy_dfa_loading() {
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
    fn test_rate_limiting_window() {
        let table = DFATable {
            states: vec![0, 1],
            start: 0,
            accepting: vec![0, 1],
            transitions: vec![
                Transition {
                    from_state: 0,
                    event: "call(tool1,hash1)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "call(tool1,hash2)".to_string(),
                    to_state: 1,
                },
                Transition {
                    from_state: 1,
                    event: "call(tool1,hash3)".to_string(),
                    to_state: 0,
                },
            ],
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
        assert_eq!(interpreter.current_state(), 1);

        // The existing closed-window contract includes the event at t=1000.
        // At t=2001 that event expires, and the exact transition is permitted.
        assert!(interpreter.process_event("call(tool1,hash3)", 2001).is_ok());
        assert_eq!(interpreter.current_state(), 0);
    }

    #[test]
    fn test_nonzero_start_and_exact_transition() {
        let table = DFATable {
            states: vec![7, 42],
            start: 42,
            accepting: vec![7],
            transitions: vec![Transition {
                from_state: 42,
                event: "call(tool1,hash1)".to_string(),
                to_state: 7,
            }],
            rate_limits: vec![],
        };
        let mut interpreter = DFAInterpreter::from_table(table);
        assert_eq!(interpreter.current_state(), 42);
        assert!(!interpreter.is_accepting());
        assert!(interpreter.process_event("call(tool1,hash2)", 1000).is_err());
        assert_eq!(interpreter.current_state(), 42);
        assert!(interpreter.process_event("call(tool1,hash1)", 1001).is_ok());
        assert!(interpreter.is_accepting());
        interpreter.reset();
        assert_eq!(interpreter.current_state(), 42);
    }

    #[test]
    fn test_ambiguous_policy_is_rejected_at_load_and_execution() {
        let table = DFATable {
            states: vec![0, 1],
            start: 0,
            accepting: vec![0, 1],
            transitions: vec![
                Transition { from_state: 0, event: "log(x)".into(), to_state: 0 },
                Transition { from_state: 0, event: "log(x)".into(), to_state: 1 },
            ],
            rate_limits: vec![],
        };
        let mut interpreter = DFAInterpreter::from_table(table.clone());
        assert!(interpreter.validate().is_err());
        assert!(!interpreter.is_accepting());
        assert!(interpreter.process_event("log(x)", 1000).is_err());

        let file = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(file.path(), serde_json::to_vec(&table).unwrap()).unwrap();
        assert!(DFAInterpreter::from_file(file.path()).is_err());
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
