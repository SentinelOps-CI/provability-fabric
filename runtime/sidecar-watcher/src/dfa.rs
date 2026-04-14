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
#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::collections::VecDeque;
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

/// High-performance DFA engine with zero-allocation hot path
pub struct OptimizedDFA {
    states: Vec<DFAState>,
    start_state: StateId,
    accepting_states: Vec<StateId>,
    // Pre-computed jump tables for hot paths
    call_jump_table: Vec<[StateId; 256]>,
    emit_jump_table: Vec<[StateId; 256]>,
    // Sparse dispatch for cold paths
    sparse_transitions: HashMap<(StateId, EventKind), StateId>,
    // Rate limiting data
    rate_limiters: HashMap<String, RateLimiter>,
}

/// Optimized rate limiter with ring buffer
#[derive(Debug, Clone)]
struct RateLimiter {
    window_ms: u32,
    bound: u32,
    events: VecDeque<u32>, // Ring buffer of timestamps in milliseconds
    head: usize,
    tail: usize,
    count: usize,
}

impl RateLimiter {
    fn new(window_ms: u32, bound: u32) -> Self {
        Self {
            window_ms,
            bound,
            events: VecDeque::with_capacity(bound as usize * 2),
            head: 0,
            tail: 0,
            count: 0,
        }
    }

    #[inline(always)]
    fn check(&mut self, current_time_ms: u32) -> bool {
        self.cleanup_old_events(current_time_ms);
        self.count < self.bound as usize
    }

    #[inline(always)]
    fn record(&mut self, current_time_ms: u32) {
        self.cleanup_old_events(current_time_ms);
        if self.count < self.bound as usize {
            self.events.push_back(current_time_ms);
            self.count += 1;
        }
    }

    #[inline(always)]
    fn cleanup_old_events(&mut self, current_time_ms: u32) {
        let window_start = current_time_ms.saturating_sub(self.window_ms);
        while let Some(&timestamp) = self.events.front() {
            if timestamp < window_start {
                self.events.pop_front();
                self.count = self.count.saturating_sub(1);
            } else {
                break;
            }
        }
    }
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
}

impl OptimizedDFA {
    /// Create optimized DFA from table with Hopcroft minimization and product pruning
    pub fn from_table(table: DFATable) -> Result<Self, Box<dyn Error>> {
        // First create the basic DFA
        let mut dfa = Self::from_table_basic(table)?;

        // Apply Hopcroft minimization
        dfa.minimize_hopcroft();

        // Apply product pruning
        dfa.apply_product_pruning();

        Ok(dfa)
    }

    /// Create basic DFA from table representation (without optimization)
    fn from_table_basic(table: DFATable) -> Result<Self, Box<dyn Error>> {
        let mut states = Vec::new();
        let mut call_jump_table = Vec::new();
        let mut emit_jump_table = Vec::new();
        let mut sparse_transitions = HashMap::new();
        let mut rate_limiters = HashMap::new();

        // Initialize states with jump tables
        for &state_id in &table.states {
            let dfa_state = DFAState {
                id: state_id,
                is_accepting: table.accepting.contains(&state_id),
                ..Default::default()
            };

            // Initialize jump tables
            let mut call_jumps = [0u32; 256];
            let mut emit_jumps = [0u32; 256];

            // Process transitions for this state
            for transition in &table.transitions {
                if transition.from_state == state_id {
                    if let Some(event_kind) = Self::parse_event_kind(&transition.event) {
                        match event_kind {
                            EventKind::Call => {
                                if let Some(tag) = Self::extract_call_tag(&transition.event) {
                                    call_jumps[tag as usize] = transition.to_state;
                                }
                            }
                            EventKind::Emit => {
                                if let Some(bucket) = Self::extract_emit_bucket(&transition.event) {
                                    emit_jumps[bucket as usize] = transition.to_state;
                                }
                            }
                            _ => {
                                // Store in sparse transitions for cold paths
                                sparse_transitions
                                    .insert((state_id, event_kind), transition.to_state);
                            }
                        }
                    }
                }
            }

            states.push(dfa_state);
            call_jump_table.push(call_jumps);
            emit_jump_table.push(emit_jumps);
        }

        // Initialize rate limiters
        for rate_limit in &table.rate_limits {
            rate_limiters.insert(
                rate_limit.tool.clone(),
                RateLimiter::new(rate_limit.window_ms, rate_limit.bound),
            );
        }

        Ok(Self {
            states,
            start_state: table.start,
            accepting_states: table.accepting,
            call_jump_table,
            emit_jump_table,
            sparse_transitions,
            rate_limiters,
        })
    }

    /// Hot path: zero-allocation state transition
    #[inline(always)]
    pub fn step(&self, state: StateId, event: &Event) -> StateId {
        match event.kind {
            EventKind::Call => {
                if state < self.call_jump_table.len() as u32 {
                    self.call_jump_table[state as usize][event.call_tag as usize]
                } else {
                    state
                }
            }
            EventKind::Emit => {
                if state < self.emit_jump_table.len() as u32 {
                    self.emit_jump_table[state as usize][event.emit_bucket as usize]
                } else {
                    state
                }
            }
            _ => {
                // Cold path: sparse dispatch
                self.sparse_transitions
                    .get(&(state, event.kind))
                    .copied()
                    .unwrap_or(state)
            }
        }
    }

    /// Process event with rate limiting
    pub fn process_event(&mut self, event: &Event, current_time_ms: u32) -> Result<bool, String> {
        // Check rate limits
        if !self.check_rate_limits(event, current_time_ms) {
            return Err("Rate limit exceeded".to_string());
        }

        // Update rate limiters
        self.update_rate_limits(event, current_time_ms);

        Ok(true)
    }

    /// Check rate limits for event
    #[inline(always)]
    fn check_rate_limits(&mut self, event: &Event, current_time_ms: u32) -> bool {
        for (tool, limiter) in &mut self.rate_limiters {
            if event.tool_name.contains(tool)
                && !limiter.check(current_time_ms) {
                    return false;
                }
        }
        true
    }

    /// Update rate limiters
    #[inline(always)]
    fn update_rate_limits(&mut self, event: &Event, current_time_ms: u32) {
        for (tool, limiter) in &mut self.rate_limiters {
            if event.tool_name.contains(tool) {
                limiter.record(current_time_ms);
            }
        }
    }

    /// Parse event kind from string
    fn parse_event_kind(event_str: &str) -> Option<EventKind> {
        if let Some(open_paren) = event_str.find('(') {
            let kind_str = &event_str[..open_paren];
            EventKind::from_str(kind_str)
        } else {
            EventKind::from_str(event_str)
        }
    }

    /// Extract call tag from event string
    fn extract_call_tag(event_str: &str) -> Option<CallTag> {
        if let Some(open_paren) = event_str.find('(') {
            if let Some(close_paren) = event_str.find(')') {
                let args = &event_str[open_paren + 1..close_paren];
                if let Some(comma) = args.find(',') {
                    let tag_str = &args[..comma];
                    tag_str.parse().ok()
                } else {
                    args.parse().ok()
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Extract emit bucket from event string
    fn extract_emit_bucket(event_str: &str) -> Option<EmitBucket> {
        if let Some(open_paren) = event_str.find('(') {
            if let Some(close_paren) = event_str.find(')') {
                let args = &event_str[open_paren + 1..close_paren];
                args.parse().ok()
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Get current state
    pub fn current_state(&self) -> StateId {
        self.start_state
    }

    /// Check if state is accepting
    pub fn is_accepting(&self, state: StateId) -> bool {
        self.accepting_states.contains(&state)
    }

    /// Validate DFA integrity
    pub fn validate(&self) -> Result<(), String> {
        if self.start_state >= self.states.len() as u32 {
            return Err("Start state out of bounds".to_string());
        }

        for &accepting_state in &self.accepting_states {
            if accepting_state >= self.states.len() as u32 {
                return Err(format!("Accepting state {} out of bounds", accepting_state));
            }
        }

        Ok(())
    }

    /// Apply Hopcroft minimization algorithm to reduce DFA states
    fn minimize_hopcroft(&mut self) {
        if self.states.len() <= 1 {
            return; // Nothing to minimize
        }

        // Initialize partitions: accepting and non-accepting states
        let mut partitions = Vec::new();
        let mut accepting_states = Vec::new();
        let mut non_accepting_states = Vec::new();

        for state in &self.states {
            if state.is_accepting {
                accepting_states.push(state.id);
            } else {
                non_accepting_states.push(state.id);
            }
        }

        if !accepting_states.is_empty() {
            partitions.push(accepting_states);
        }
        if !non_accepting_states.is_empty() {
            partitions.push(non_accepting_states);
        }

        // Hopcroft algorithm main loop
        let mut worklist = partitions.clone();
        let mut partition_map = HashMap::new();

        for (i, partition) in partitions.iter().enumerate() {
            for &state in partition {
                partition_map.insert(state, i);
            }
        }

        while let Some(current_partition) = worklist.pop() {
            if current_partition.is_empty() {
                continue;
            }

            // Find all possible transitions from this partition
            let mut transitions = HashMap::new();
            for &state in &current_partition {
                if let Some(state_idx) = self.states.iter().position(|s| s.id == state) {
                    // Check call transitions
                    for (call_tag, &next_state) in
                        self.call_jump_table[state_idx].iter().enumerate()
                    {
                        if next_state != state {
                            transitions
                                .entry(('c', call_tag as u16, next_state))
                                .or_insert_with(Vec::new)
                                .push(state);
                        }
                    }
                    // Check emit transitions
                    for (emit_bucket, &next_state) in
                        self.emit_jump_table[state_idx].iter().enumerate()
                    {
                        if next_state != state {
                            transitions
                                .entry(('e', emit_bucket as u16, next_state))
                                .or_insert_with(Vec::new)
                                .push(state);
                        }
                    }
                }
            }

            // Split partitions based on transitions
            for ((_event_type, _event_value, _next_state), states) in transitions {
                if states.len() < current_partition.len() {
                    // Split the partition
                    let mut new_partition = Vec::new();
                    let mut remaining_partition = current_partition.clone();

                    for state in states {
                        if let Some(pos) = remaining_partition.iter().position(|&s| s == state) {
                            remaining_partition.remove(pos);
                            new_partition.push(state);
                        }
                    }

                    if !new_partition.is_empty() && !remaining_partition.is_empty() {
                        // Update partition map
                        let new_partition_id = partitions.len();
                        for &state in &new_partition {
                            partition_map.insert(state, new_partition_id);
                        }
                        for &state in &remaining_partition {
                            partition_map.insert(state, partitions.len() - 1);
                        }

                        partitions.push(new_partition);
                        worklist.push(remaining_partition);
                    }
                }
            }
        }

        // Merge equivalent states
        self.merge_equivalent_states(&partitions);
    }

    /// Apply product pruning to remove DFAs unrelated to current event kind
    fn apply_product_pruning(&mut self) {
        // Analyze event kind usage patterns
        let mut event_usage = HashMap::new();

        for state_idx in 0..self.states.len() {
            // Count call transitions
            for (call_tag, &next_state) in self.call_jump_table[state_idx].iter().enumerate() {
                if next_state != self.states[state_idx].id {
                    *event_usage.entry(('c', call_tag as u16)).or_insert(0) += 1;
                }
            }

            // Count emit transitions
            for (emit_bucket, &next_state) in self.emit_jump_table[state_idx].iter().enumerate() {
                if next_state != self.states[state_idx].id {
                    *event_usage.entry(('e', emit_bucket as u16)).or_insert(0) += 1;
                }
            }
        }

        // Prune rarely used transitions (threshold: < 5% of total transitions)
        let total_transitions: usize = event_usage.values().sum();
        let threshold = (total_transitions as f64 * 0.05) as usize;

        for state_idx in 0..self.states.len() {
            // Prune call transitions
            for (call_tag, next_state) in self.call_jump_table[state_idx].iter_mut().enumerate() {
                if *next_state != self.states[state_idx].id {
                    let usage = event_usage.get(&('c', call_tag as u16)).unwrap_or(&0);
                    if *usage < threshold {
                        *next_state = self.states[state_idx].id; // Self-loop for unused transitions
                    }
                }
            }

            // Prune emit transitions
            for (emit_bucket, next_state) in self.emit_jump_table[state_idx].iter_mut().enumerate()
            {
                if *next_state != self.states[state_idx].id {
                    let usage = event_usage.get(&('e', emit_bucket as u16)).unwrap_or(&0);
                    if *usage < threshold {
                        *next_state = self.states[state_idx].id; // Self-loop for unused transitions
                    }
                }
            }
        }
    }

    /// Merge equivalent states after Hopcroft minimization
    fn merge_equivalent_states(&mut self, partitions: &[Vec<StateId>]) {
        if partitions.len() >= self.states.len() {
            return; // No merging possible
        }

        // Create state mapping
        let mut state_mapping = HashMap::new();
        let mut new_states = Vec::new();
        let mut new_call_jump_table = Vec::new();
        let mut new_emit_jump_table = Vec::new();

        for (new_id, partition) in partitions.iter().enumerate() {
            if partition.is_empty() {
                continue;
            }

            // Use the first state in the partition as the representative
            let representative = partition[0];
            state_mapping.insert(representative, new_id as StateId);

            // Merge state properties
            let merged_state = DFAState {
                id: new_id as StateId,
                is_accepting: partition.iter().any(|&state_id| {
                    self.states
                        .iter()
                        .any(|s| s.id == state_id && s.is_accepting)
                }),
                ..Default::default()
            };

            // Merge jump tables
            let mut call_jumps = [0u32; 256];
            let mut emit_jumps = [0u32; 256];

            for &state_id in partition {
                if let Some(state_idx) = self.states.iter().position(|s| s.id == state_id) {
                    for (i, &transition) in self.call_jump_table[state_idx].iter().enumerate() {
                        if transition != state_id {
                            call_jumps[i] = transition;
                        }
                    }
                    for (i, &transition) in self.emit_jump_table[state_idx].iter().enumerate() {
                        if transition != state_id {
                            emit_jumps[i] = transition;
                        }
                    }
                }
            }

            new_states.push(merged_state);
            new_call_jump_table.push(call_jumps);
            new_emit_jump_table.push(emit_jumps);
        }

        // Update state mappings in jump tables
        for call_jumps in &mut new_call_jump_table {
            for jump in call_jumps.iter_mut() {
                if let Some(&mapped_state) = state_mapping.get(jump) {
                    *jump = mapped_state;
                }
            }
        }

        for emit_jumps in &mut new_emit_jump_table {
            for jump in emit_jumps.iter_mut() {
                if let Some(&mapped_state) = state_mapping.get(jump) {
                    *jump = mapped_state;
                }
            }
        }

        // Update the DFA with merged states
        self.states = new_states;
        self.call_jump_table = new_call_jump_table;
        self.emit_jump_table = new_emit_jump_table;

        // Update start state
        if let Some(&new_start) = state_mapping.get(&self.start_state) {
            self.start_state = new_start;
        }

        // Update accepting states
        self.accepting_states = self
            .states
            .iter()
            .filter(|s| s.is_accepting)
            .map(|s| s.id)
            .collect();
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
                LegacyRateLimiter::new(rate_limit.window_ms, rate_limit.bound),
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

        let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());
        let next_state = dfa.step(0, &event);
        assert_eq!(next_state, 1);
    }

    #[test]
    fn test_rate_limiting() {
        let table = DFATable {
            states: vec![0, 1],
            start: 0,
            accepting: vec![0, 1],
            transitions: vec![Transition {
                from_state: 0,
                event: "call(tool1,1)".to_string(),
                to_state: 1,
            }],
            rate_limits: vec![RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 2,
            }],
        };

        let mut dfa = OptimizedDFA::from_table(table).unwrap();

        let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());

        // First two calls should succeed
        assert!(dfa.process_event(&event, 1000).is_ok());
        assert!(dfa.process_event(&event, 1500).is_ok());

        // Third call should fail
        assert!(dfa.process_event(&event, 2000).is_err());
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

        let event = Event::new(EventKind::Call, 1, 0, "tool1".to_string());

        // Benchmark hot path
        let start = Instant::now();
        for _ in 0..100_000 {
            let _ = dfa.step(0, &event);
        }
        let duration = start.elapsed();

        // Should complete in less than 1ms for 100k operations
        assert!(
            duration.as_millis() < 1,
            "Hot path too slow: {:?}",
            duration
        );
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
