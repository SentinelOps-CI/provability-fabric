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
use std::collections::{BinaryHeap, VecDeque};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// Event priority levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Priority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// Event to be scheduled
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ScheduledEvent {
    pub id: String,
    pub priority: Priority,
    pub timestamp: Instant,
    pub session_id: String,
    pub event_type: String,
    pub payload: serde_json::Value,
    pub sequence_number: u64,
}

impl PartialEq for ScheduledEvent {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ScheduledEvent {}

impl PartialOrd for ScheduledEvent {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ScheduledEvent {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Higher priority first, then FIFO within same priority
        other
            .priority
            .cmp(&self.priority)
            .then(self.timestamp.cmp(&other.timestamp))
            .then(self.sequence_number.cmp(&other.sequence_number))
    }
}

/// Scheduler configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerConfig {
    pub max_concurrent_sessions: usize,
    pub max_events_per_session: usize,
    pub default_timeout: Duration,
    pub enable_two_queue: bool,
    pub fifo_merge_threshold: usize,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            max_concurrent_sessions: 20,
            max_events_per_session: 100000,
            default_timeout: Duration::from_secs(300), // 5 minutes
            enable_two_queue: false,
            fifo_merge_threshold: 1000,
        }
    }
}

/// SGEQ (Strict Global Event Queue) scheduler
pub struct SGEQScheduler {
    config: SchedulerConfig,
    event_queue: BinaryHeap<ScheduledEvent>,
    session_events: Arc<Mutex<HashMap<String, VecDeque<ScheduledEvent>>>>,
    sequence_counter: Arc<Mutex<u64>>,
    active_sessions: Arc<Mutex<HashSet<String>>>,
}

impl SGEQScheduler {
    /// Create new SGEQ scheduler
    pub fn new(config: SchedulerConfig) -> Self {
        Self {
            config,
            event_queue: BinaryHeap::new(),
            session_events: Arc::new(Mutex::new(HashMap::new())),
            sequence_counter: Arc::new(Mutex::new(0)),
            active_sessions: Arc::new(Mutex::new(HashSet::new())),
        }
    }

    /// Schedule an event
    pub fn schedule_event(&mut self, event: ScheduledEvent) -> Result<(), String> {
        // Check session limits
        if self.active_sessions.lock().unwrap().len() >= self.config.max_concurrent_sessions {
            return Err("Maximum concurrent sessions exceeded".to_string());
        }

        // Check per-session event limits
        let session_events = self.session_events.lock().unwrap();
        if let Some(events) = session_events.get(&event.session_id) {
            if events.len() >= self.config.max_events_per_session {
                return Err("Maximum events per session exceeded".to_string());
            }
        }

        // Add to global queue
        self.event_queue.push(event.clone());

        // Add to session-specific queue
        let mut session_events = self.session_events.lock().unwrap();
        session_events
            .entry(event.session_id.clone())
            .or_insert_with(VecDeque::new)
            .push_back(event);

        // Mark session as active
        self.active_sessions
            .lock()
            .unwrap()
            .insert(event.session_id);

        Ok(())
    }

    /// Get next event to process
    pub fn next_event(&mut self) -> Option<ScheduledEvent> {
        self.event_queue.pop()
    }

    /// Get events for a specific session
    pub fn get_session_events(&self, session_id: &str) -> Vec<ScheduledEvent> {
        let session_events = self.session_events.lock().unwrap();
        session_events
            .get(session_id)
            .map(|events| events.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Complete a session
    pub fn complete_session(&mut self, session_id: &str) {
        self.active_sessions.lock().unwrap().remove(session_id);
        let mut session_events = self.session_events.lock().unwrap();
        session_events.remove(session_id);
    }

    /// Get scheduler statistics
    pub fn get_stats(&self) -> SchedulerStats {
        let active_sessions = self.active_sessions.lock().unwrap().len();
        let total_events = self.event_queue.len();
        let session_events = self.session_events.lock().unwrap();
        let total_sessions = session_events.len();

        SchedulerStats {
            active_sessions,
            total_events,
            total_sessions,
            max_concurrent_sessions: self.config.max_concurrent_sessions,
            max_events_per_session: self.config.max_events_per_session,
        }
    }
}

/// Two-queue scheduler with FIFO merge
pub struct TwoQueueScheduler {
    config: SchedulerConfig,
    priority_queue: BinaryHeap<ScheduledEvent>,
    fifo_queue: VecDeque<ScheduledEvent>,
    session_events: Arc<Mutex<HashMap<String, VecDeque<ScheduledEvent>>>>,
    sequence_counter: Arc<Mutex<u64>>,
    active_sessions: Arc<Mutex<HashSet<String>>>,
    merge_triggered: bool,
}

impl TwoQueueScheduler {
    /// Create new two-queue scheduler
    pub fn new(config: SchedulerConfig) -> Self {
        Self {
            config,
            priority_queue: BinaryHeap::new(),
            fifo_queue: VecDeque::new(),
            session_events: Arc::new(Mutex::new(HashMap::new())),
            sequence_counter: Arc::new(Mutex::new(0)),
            active_sessions: Arc::new(Mutex::new(HashSet::new())),
            merge_triggered: false,
        }
    }

    /// Schedule an event
    pub fn schedule_event(&mut self, event: ScheduledEvent) -> Result<(), String> {
        // Check session limits
        if self.active_sessions.lock().unwrap().len() >= self.config.max_concurrent_sessions {
            return Err("Maximum concurrent sessions exceeded".to_string());
        }

        // Check per-session event limits
        let session_events = self.session_events.lock().unwrap();
        if let Some(events) = session_events.get(&event.session_id) {
            if events.len() >= self.config.max_events_per_session {
                return Err("Maximum events per session exceeded".to_string());
            }
        }

        // Route to appropriate queue based on priority
        if event.priority == Priority::Critical || event.priority == Priority::High {
            self.priority_queue.push(event.clone());
        } else {
            self.fifo_queue.push_back(event.clone());
        }

        // Add to session-specific queue
        let mut session_events = self.session_events.lock().unwrap();
        session_events
            .entry(event.session_id.clone())
            .or_insert_with(VecDeque::new)
            .push_back(event);

        // Mark session as active
        self.active_sessions
            .lock()
            .unwrap()
            .insert(event.session_id);

        // Check if FIFO merge should be triggered
        if !self.merge_triggered && self.fifo_queue.len() >= self.config.fifo_merge_threshold {
            self.merge_triggered = true;
        }

        Ok(())
    }

    /// Get next event to process
    pub fn next_event(&mut self) -> Option<ScheduledEvent> {
        // If merge is triggered, process FIFO queue first
        if self.merge_triggered && !self.fifo_queue.is_empty() {
            return self.fifo_queue.pop_front();
        }

        // Otherwise, process priority queue first
        if !self.priority_queue.is_empty() {
            return self.priority_queue.pop();
        }

        // Fall back to FIFO queue
        self.fifo_queue.pop_front()
    }

    /// Trigger FIFO merge
    pub fn trigger_fifo_merge(&mut self) {
        self.merge_triggered = true;
    }

    /// Reset FIFO merge
    pub fn reset_fifo_merge(&mut self) {
        self.merge_triggered = false;
    }

    /// Get events for a specific session
    pub fn get_session_events(&self, session_id: &str) -> Vec<ScheduledEvent> {
        let session_events = self.session_events.lock().unwrap();
        session_events
            .get(session_id)
            .map(|events| events.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Complete a session
    pub fn complete_session(&mut self, session_id: &str) {
        self.active_sessions.lock().unwrap().remove(session_id);
        let mut session_events = self.session_events.lock().unwrap();
        session_events.remove(session_id);
    }

    /// Get scheduler statistics
    pub fn get_stats(&self) -> TwoQueueSchedulerStats {
        let active_sessions = self.active_sessions.lock().unwrap().len();
        let priority_events = self.priority_queue.len();
        let fifo_events = self.fifo_queue.len();
        let total_events = priority_events + fifo_events;
        let session_events = self.session_events.lock().unwrap();
        let total_sessions = session_events.len();

        TwoQueueSchedulerStats {
            active_sessions,
            total_events,
            priority_events,
            fifo_events,
            total_sessions,
            merge_triggered: self.merge_triggered,
            max_concurrent_sessions: self.config.max_concurrent_sessions,
            max_events_per_session: self.config.max_events_per_session,
        }
    }
}

/// Scheduler statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulerStats {
    pub active_sessions: usize,
    pub total_events: usize,
    pub total_sessions: usize,
    pub max_concurrent_sessions: usize,
    pub max_events_per_session: usize,
}

/// Two-queue scheduler statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TwoQueueSchedulerStats {
    pub active_sessions: usize,
    pub total_events: usize,
    pub priority_events: usize,
    pub fifo_events: usize,
    pub total_sessions: usize,
    pub merge_triggered: bool,
    pub max_concurrent_sessions: usize,
    pub max_events_per_session: usize,
}

/// Scheduler trait for common operations
pub trait Scheduler {
    fn schedule_event(&mut self, event: ScheduledEvent) -> Result<(), String>;
    fn next_event(&mut self) -> Option<ScheduledEvent>;
    fn get_session_events(&self, session_id: &str) -> Vec<ScheduledEvent>;
    fn complete_session(&mut self, session_id: &str);
}

impl Scheduler for SGEQScheduler {
    fn schedule_event(&mut self, event: ScheduledEvent) -> Result<(), String> {
        self.schedule_event(event)
    }

    fn next_event(&mut self) -> Option<ScheduledEvent> {
        self.next_event()
    }

    fn get_session_events(&self, session_id: &str) -> Vec<ScheduledEvent> {
        self.get_session_events(session_id)
    }

    fn complete_session(&mut self, session_id: &str) {
        self.complete_session(session_id)
    }
}

impl Scheduler for TwoQueueScheduler {
    fn schedule_event(&mut self, event: ScheduledEvent) -> Result<(), String> {
        self.schedule_event(event)
    }

    fn next_event(&mut self) -> Option<ScheduledEvent> {
        self.next_event()
    }

    fn get_session_events(&self, session_id: &str) -> Vec<ScheduledEvent> {
        self.get_session_events(session_id)
    }

    fn complete_session(&mut self, session_id: &str) {
        self.complete_session(session_id)
    }
}

/// Event builder for creating scheduled events
pub struct EventBuilder {
    id: String,
    priority: Priority,
    timestamp: Instant,
    session_id: String,
    event_type: String,
    payload: serde_json::Value,
    sequence_number: u64,
}

impl EventBuilder {
    /// Create new event builder
    pub fn new(event_type: String, session_id: String) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            priority: Priority::Normal,
            timestamp: Instant::now(),
            session_id,
            event_type,
            payload: serde_json::Value::Null,
            sequence_number: 0,
        }
    }

    /// Set event ID
    pub fn with_id(mut self, id: String) -> Self {
        self.id = id;
        self
    }

    /// Set priority
    pub fn with_priority(mut self, priority: Priority) -> Self {
        self.priority = priority;
        self
    }

    /// Set timestamp
    pub fn with_timestamp(mut self, timestamp: Instant) -> Self {
        self.timestamp = timestamp;
        self
    }

    /// Set payload
    pub fn with_payload(mut self, payload: serde_json::Value) -> Self {
        self.payload = payload;
        self
    }

    /// Set sequence number
    pub fn with_sequence_number(mut self, sequence_number: u64) -> Self {
        self.sequence_number = sequence_number;
        self
    }

    /// Build the event
    pub fn build(self) -> ScheduledEvent {
        ScheduledEvent {
            id: self.id,
            priority: self.priority,
            timestamp: self.timestamp,
            session_id: self.session_id,
            event_type: self.event_type,
            payload: self.payload,
            sequence_number: self.sequence_number,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::time::Duration;

    #[test]
    fn test_sgeq_scheduler_basic() {
        let config = SchedulerConfig::default();
        let mut scheduler = SGEQScheduler::new(config);

        let event1 = EventBuilder::new("test1".to_string(), "session1".to_string())
            .with_priority(Priority::High)
            .build();

        let event2 = EventBuilder::new("test2".to_string(), "session1".to_string())
            .with_priority(Priority::Low)
            .build();

        scheduler.schedule_event(event1.clone()).unwrap();
        scheduler.schedule_event(event2.clone()).unwrap();

        // High priority event should come first
        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event1.id);

        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event2.id);
    }

    #[test]
    fn test_two_queue_scheduler() {
        let mut config = SchedulerConfig::default();
        config.enable_two_queue = true;
        config.fifo_merge_threshold = 2;

        let mut scheduler = TwoQueueScheduler::new(config);

        let event1 = EventBuilder::new("test1".to_string(), "session1".to_string())
            .with_priority(Priority::Critical)
            .build();

        let event2 = EventBuilder::new("test2".to_string(), "session1".to_string())
            .with_priority(Priority::Normal)
            .build();

        let event3 = EventBuilder::new("test3".to_string(), "session1".to_string())
            .with_priority(Priority::Normal)
            .build();

        scheduler.schedule_event(event1.clone()).unwrap();
        scheduler.schedule_event(event2.clone()).unwrap();
        scheduler.schedule_event(event3.clone()).unwrap();

        // Critical event should come first
        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event1.id);

        // Then FIFO events in order
        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event2.id);

        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event3.id);
    }

    #[test]
    fn test_session_limits() {
        let mut config = SchedulerConfig::default();
        config.max_concurrent_sessions = 1;
        config.max_events_per_session = 2;

        let mut scheduler = SGEQScheduler::new(config);

        let event1 = EventBuilder::new("test1".to_string(), "session1".to_string()).build();
        let event2 = EventBuilder::new("test2".to_string(), "session1".to_string()).build();
        let event3 = EventBuilder::new("test3".to_string(), "session1".to_string()).build();

        scheduler.schedule_event(event1).unwrap();
        scheduler.schedule_event(event2).unwrap();

        // Third event should fail due to per-session limit
        let result = scheduler.schedule_event(event3);
        assert!(result.is_err());
    }

    #[test]
    fn test_fifo_merge_trigger() {
        let mut config = SchedulerConfig::default();
        config.enable_two_queue = true;
        config.fifo_merge_threshold = 3;

        let mut scheduler = TwoQueueScheduler::new(config);

        let event1 = EventBuilder::new("test1".to_string(), "session1".to_string())
            .with_priority(Priority::Normal)
            .build();

        let event2 = EventBuilder::new("test2".to_string(), "session1".to_string())
            .with_priority(Priority::Normal)
            .build();

        let event3 = EventBuilder::new("test3".to_string(), "session1".to_string())
            .with_priority(Priority::Normal)
            .build();

        scheduler.schedule_event(event1.clone()).unwrap();
        scheduler.schedule_event(event2.clone()).unwrap();
        scheduler.schedule_event(event3.clone()).unwrap();

        // FIFO merge should be triggered
        assert!(scheduler.get_stats().merge_triggered);

        // Events should be processed in FIFO order
        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event1.id);

        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event2.id);

        let next = scheduler.next_event().unwrap();
        assert_eq!(next.id, event3.id);
    }

    #[test]
    fn test_concurrency_stress() {
        let mut config = SchedulerConfig::default();
        config.max_concurrent_sessions = 20;
        config.max_events_per_session = 100000;

        let mut scheduler = SGEQScheduler::new(config);

        // Create 20 sessions with 100k events each
        for session_id in 0..20 {
            for event_id in 0..100000 {
                let event = EventBuilder::new(
                    format!("event_{}", event_id),
                    format!("session_{}", session_id),
                )
                .with_priority(Priority::Normal)
                .build();

                scheduler.schedule_event(event).unwrap();
            }
        }

        let stats = scheduler.get_stats();
        assert_eq!(stats.active_sessions, 20);
        assert_eq!(stats.total_events, 2000000);
        assert_eq!(stats.total_sessions, 20);
    }

    #[test]
    fn test_concurrency_stress_with_priority_mixing() {
        let mut config = SchedulerConfig::default();
        config.max_concurrent_sessions = 20;
        config.max_events_per_session = 100000;

        let mut scheduler = SGEQScheduler::new(config);

        // Create 20 sessions with mixed priority events
        for session_id in 0..20 {
            for event_id in 0..100000 {
                let priority = match event_id % 4 {
                    0 => Priority::Low,
                    1 => Priority::Normal,
                    2 => Priority::High,
                    _ => Priority::Critical,
                };

                let event = EventBuilder::new(
                    format!("event_{}", event_id),
                    format!("session_{}", session_id),
                )
                .with_priority(priority)
                .with_sequence_number(event_id as u64)
                .build();

                scheduler.schedule_event(event).unwrap();
            }
        }

        let stats = scheduler.get_stats();
        assert_eq!(stats.active_sessions, 20);
        assert_eq!(stats.total_events, 2000000);
        assert_eq!(stats.total_sessions, 20);

        // Verify that high priority events are processed first
        let mut processed_events = Vec::new();
        let mut event_count = 0;

        while let Some(event) = scheduler.next_event() {
            processed_events.push(event);
            event_count += 1;
            if event_count >= 1000 {
                // Check first 1000 events
                break;
            }
        }

        // Verify priority ordering in processed events
        for i in 1..processed_events.len() {
            let prev_priority = processed_events[i - 1].priority as u8;
            let curr_priority = processed_events[i].priority as u8;
            assert!(
                prev_priority >= curr_priority,
                "Priority ordering violated: {} < {}",
                prev_priority,
                curr_priority
            );
        }
    }

    #[test]
    fn test_two_queue_concurrency_stress() {
        let mut config = SchedulerConfig::default();
        config.enable_two_queue = true;
        config.max_concurrent_sessions = 20;
        config.max_events_per_session = 100000;
        config.fifo_merge_threshold = 1000;

        let mut scheduler = TwoQueueScheduler::new(config);

        // Create 20 sessions with mixed priority events
        for session_id in 0..20 {
            for event_id in 0..100000 {
                let priority = match event_id % 4 {
                    0 => Priority::Low,
                    1 => Priority::Normal,
                    2 => Priority::High,
                    _ => Priority::Critical,
                };

                let event = EventBuilder::new(
                    format!("event_{}", event_id),
                    format!("session_{}", session_id),
                )
                .with_priority(priority)
                .with_sequence_number(event_id as u64)
                .build();

                scheduler.schedule_event(event).unwrap();
            }
        }

        let stats = scheduler.get_stats();
        assert_eq!(stats.active_sessions, 20);
        assert_eq!(stats.total_events, 2000000);
        assert_eq!(stats.total_sessions, 20);
        assert!(
            stats.merge_triggered,
            "FIFO merge should be triggered with 100k events"
        );

        // Verify that events are processed correctly with FIFO merge
        let mut processed_events = Vec::new();
        let mut event_count = 0;

        while let Some(event) = scheduler.next_event() {
            processed_events.push(event);
            event_count += 1;
            if event_count >= 1000 {
                // Check first 1000 events
                break;
            }
        }

        // Verify that critical and high priority events come first
        let critical_high_count = processed_events
            .iter()
            .filter(|e| e.priority == Priority::Critical || e.priority == Priority::High)
            .count();

        // At least 50% of first 1000 events should be high priority
        assert!(
            critical_high_count >= 500,
            "Expected at least 500 high priority events, got {}",
            critical_high_count
        );
    }

    #[test]
    fn test_event_ordering() {
        let config = SchedulerConfig::default();
        let mut scheduler = SGEQScheduler::new(config);

        let mut events = Vec::new();

        // Create events with different priorities and timestamps
        for i in 0..10 {
            let priority = match i % 4 {
                0 => Priority::Low,
                1 => Priority::Normal,
                2 => Priority::High,
                _ => Priority::Critical,
            };

            let event = EventBuilder::new(format!("event_{}", i), "session1".to_string())
                .with_priority(priority)
                .with_sequence_number(i as u64)
                .build();

            events.push(event.clone());
            scheduler.schedule_event(event).unwrap();
        }

        // Events should be processed in priority order
        let mut processed_events = Vec::new();
        while let Some(event) = scheduler.next_event() {
            processed_events.push(event);
        }

        // Verify priority ordering
        for i in 1..processed_events.len() {
            let prev_priority = processed_events[i - 1].priority as u8;
            let curr_priority = processed_events[i].priority as u8;
            assert!(prev_priority >= curr_priority);
        }
    }
}
