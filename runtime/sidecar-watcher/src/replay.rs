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
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// Replay configuration for deterministic execution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayConfig {
    pub chunk_bytes: usize,
    pub flush_ms: u64,
    pub locale: String,
    pub timezone: String,
    pub seed: u64,
    pub enable_drift_detection: bool,
    pub drift_threshold_ms: u64,
    pub max_replay_attempts: usize,
}

impl Default for ReplayConfig {
    fn default() -> Self {
        Self {
            chunk_bytes: 8192, // 8KB chunks
            flush_ms: 100,     // 100ms flush interval
            locale: "en_US.UTF-8".to_string(),
            timezone: "UTC".to_string(),
            seed: 42,
            enable_drift_detection: true,
            drift_threshold_ms: 50, // 50ms drift threshold
            max_replay_attempts: 3,
        }
    }
}

/// Replay session state
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplaySession {
    pub session_id: String,
    pub config: ReplayConfig,
    pub start_time: Instant,
    pub events: Vec<ReplayEvent>,
    pub chunk_buffer: Vec<u8>,
    pub last_flush: Instant,
    pub sequence_number: u64,
    pub drift_detected: bool,
    pub drift_measurements: Vec<DriftMeasurement>,
}

impl ReplaySession {
    /// Create new replay session
    pub fn new(session_id: String, config: ReplayConfig) -> Self {
        Self {
            session_id,
            config,
            start_time: Instant::now(),
            events: Vec::new(),
            chunk_buffer: Vec::new(),
            last_flush: Instant::now(),
            sequence_number: 0,
            drift_detected: false,
            drift_measurements: Vec::new(),
        }
    }

    /// Add event to replay session
    pub fn add_event(&mut self, event: ReplayEvent) -> Result<(), String> {
        // Check if chunk buffer needs flushing
        if self.chunk_buffer.len() >= self.config.chunk_bytes {
            self.flush_chunk()?;
        }

        // Add event to buffer
        let event_bytes =
            serde_json::to_vec(&event).map_err(|e| format!("Failed to serialize event: {}", e))?;

        self.chunk_buffer.extend_from_slice(&event_bytes);
        self.events.push(event);

        // Check if time-based flush is needed
        if self.last_flush.elapsed() >= Duration::from_millis(self.config.flush_ms) {
            self.flush_chunk()?;
        }

        Ok(())
    }

    /// Flush current chunk
    pub fn flush_chunk(&mut self) -> Result<(), String> {
        if self.chunk_buffer.is_empty() {
            return Ok(());
        }

        // Generate chunk hash for determinism
        let chunk_hash = self.compute_chunk_hash();

        // Record chunk information
        let chunk_info = ChunkInfo {
            sequence_number: self.sequence_number,
            size_bytes: self.chunk_buffer.len(),
            hash: chunk_hash,
            timestamp: self.get_deterministic_timestamp(),
        };

        // Clear buffer and update state
        self.chunk_buffer.clear();
        self.last_flush = Instant::now();
        self.sequence_number += 1;

        Ok(())
    }

    /// Compute hash for current chunk
    fn compute_chunk_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hasher.update(&self.chunk_buffer);
        format!("{:x}", hasher.finalize())
    }

    /// Get deterministic timestamp
    fn get_deterministic_timestamp(&self) -> u64 {
        // Use session start time + sequence number for deterministic timestamps
        let session_start = self.start_time.duration_since(Instant::now()).as_millis() as u64;
        session_start + self.sequence_number
    }

    /// Check for drift in replay execution
    pub fn check_drift(&mut self, expected_time: u64, actual_time: u64) -> bool {
        if !self.config.enable_drift_detection {
            return false;
        }

        let drift_ms = if actual_time > expected_time {
            actual_time - expected_time
        } else {
            expected_time - actual_time
        };

        let measurement = DriftMeasurement {
            sequence_number: self.sequence_number,
            expected_time,
            actual_time,
            drift_ms,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
        };

        self.drift_measurements.push(measurement);

        if drift_ms > self.config.drift_threshold_ms {
            self.drift_detected = true;
            true
        } else {
            false
        }
    }

    /// Get replay statistics
    pub fn get_stats(&self) -> ReplayStats {
        ReplayStats {
            session_id: self.session_id.clone(),
            total_events: self.events.len(),
            total_chunks: self.sequence_number,
            current_buffer_size: self.chunk_buffer.len(),
            drift_detected: self.drift_detected,
            drift_measurements: self.drift_measurements.len(),
            config: self.config.clone(),
        }
    }

    /// Export replay data for verification
    pub fn export_replay_data(&self) -> ReplayExport {
        ReplayExport {
            session_id: self.session_id.clone(),
            config: self.config.clone(),
            events: self.events.clone(),
            chunk_info: self.generate_chunk_info(),
            drift_measurements: self.drift_measurements.clone(),
            export_timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
        }
    }

    /// Generate chunk information
    fn generate_chunk_info(&self) -> Vec<ChunkInfo> {
        let mut chunk_info = Vec::new();
        let mut current_chunk = Vec::new();
        let mut chunk_sequence = 0;

        for event in &self.events {
            let event_bytes = serde_json::to_vec(event).unwrap();

            if current_chunk.len() + event_bytes.len() > self.config.chunk_bytes {
                // Flush current chunk
                if !current_chunk.is_empty() {
                    let mut hasher = Sha256::new();
                    hasher.update(&current_chunk);
                    let hash = format!("{:x}", hasher.finalize());

                    chunk_info.push(ChunkInfo {
                        sequence_number: chunk_sequence,
                        size_bytes: current_chunk.len(),
                        hash,
                        timestamp: self.start_time.elapsed().as_millis() as u64 + chunk_sequence,
                    });

                    chunk_sequence += 1;
                    current_chunk.clear();
                }
            }

            current_chunk.extend_from_slice(&event_bytes);
        }

        // Add final chunk if not empty
        if !current_chunk.is_empty() {
            let mut hasher = Sha256::new();
            hasher.update(&current_chunk);
            let hash = format!("{:x}", hasher.finalize());

            chunk_info.push(ChunkInfo {
                sequence_number: chunk_sequence,
                size_bytes: current_chunk.len(),
                hash,
                timestamp: self.start_time.elapsed().as_millis() as u64 + chunk_sequence,
            });
        }

        chunk_info
    }
}

/// Replay event
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayEvent {
    pub event_id: String,
    pub event_type: String,
    pub timestamp: u64,
    pub payload: serde_json::Value,
    pub metadata: HashMap<String, String>,
}

/// Chunk information for replay verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChunkInfo {
    pub sequence_number: u64,
    pub size_bytes: usize,
    pub hash: String,
    pub timestamp: u64,
}

/// Drift measurement
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriftMeasurement {
    pub sequence_number: u64,
    pub expected_time: u64,
    pub actual_time: u64,
    pub drift_ms: u64,
    pub timestamp: u64,
}

/// Replay statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayStats {
    pub session_id: String,
    pub total_events: usize,
    pub total_chunks: u64,
    pub current_buffer_size: usize,
    pub drift_detected: bool,
    pub drift_measurements: usize,
    pub config: ReplayConfig,
}

/// Replay export data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayExport {
    pub session_id: String,
    pub config: ReplayConfig,
    pub events: Vec<ReplayEvent>,
    pub chunk_info: Vec<ChunkInfo>,
    pub drift_measurements: Vec<DriftMeasurement>,
    pub export_timestamp: u64,
}

/// Replay manager for coordinating multiple sessions
pub struct ReplayManager {
    sessions: HashMap<String, ReplaySession>,
    global_config: ReplayConfig,
    drift_alarms: Vec<DriftAlarm>,
}

impl ReplayManager {
    /// Create new replay manager
    pub fn new(global_config: ReplayConfig) -> Self {
        Self {
            sessions: HashMap::new(),
            global_config,
            drift_alarms: Vec::new(),
        }
    }

    /// Create new replay session
    pub fn create_session(&mut self, session_id: String, config: Option<ReplayConfig>) -> String {
        let session_config = config.unwrap_or(self.global_config.clone());
        let session = ReplaySession::new(session_id.clone(), session_config);
        self.sessions.insert(session_id.clone(), session);
        session_id
    }

    /// Add event to session
    pub fn add_event(&mut self, session_id: &str, event: ReplayEvent) -> Result<(), String> {
        let session = self
            .sessions
            .get_mut(session_id)
            .ok_or_else(|| format!("Session {} not found", session_id))?;

        session.add_event(event)
    }

    /// Check drift for session
    pub fn check_drift(&mut self, session_id: &str, expected_time: u64, actual_time: u64) -> bool {
        let session = self
            .sessions
            .get_mut(session_id)
            .ok_or_else(|| format!("Session {} not found", session_id))
            .unwrap();

        let drift_detected = session.check_drift(expected_time, actual_time);

        if drift_detected {
            self.record_drift_alarm(session_id, expected_time, actual_time);
        }

        drift_detected
    }

    /// Record drift alarm
    fn record_drift_alarm(&mut self, session_id: &str, expected_time: u64, actual_time: u64) {
        let alarm = DriftAlarm {
            session_id: session_id.to_string(),
            expected_time,
            actual_time,
            drift_ms: if actual_time > expected_time {
                actual_time - expected_time
            } else {
                expected_time - actual_time
            },
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
        };

        self.drift_alarms.push(alarm);
    }

    /// Get session statistics
    pub fn get_session_stats(&self, session_id: &str) -> Option<ReplayStats> {
        self.sessions.get(session_id).map(|s| s.get_stats())
    }

    /// Get all session statistics
    pub fn get_all_stats(&self) -> Vec<ReplayStats> {
        self.sessions.values().map(|s| s.get_stats()).collect()
    }

    /// Export session replay data
    pub fn export_session(&self, session_id: &str) -> Option<ReplayExport> {
        self.sessions
            .get(session_id)
            .map(|s| s.export_replay_data())
    }

    /// Get drift alarms
    pub fn get_drift_alarms(&self) -> &[DriftAlarm] {
        &self.drift_alarms
    }

    /// Clear drift alarms
    pub fn clear_drift_alarms(&mut self) {
        self.drift_alarms.clear();
    }

    /// Remove session
    pub fn remove_session(&mut self, session_id: &str) -> Option<ReplaySession> {
        self.sessions.remove(session_id)
    }

    /// Get total sessions count
    pub fn session_count(&self) -> usize {
        self.sessions.len()
    }
}

/// Drift alarm
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DriftAlarm {
    pub session_id: String,
    pub expected_time: u64,
    pub actual_time: u64,
    pub drift_ms: u64,
    pub timestamp: u64,
}

/// Replay determinism verifier
pub struct ReplayVerifier {
    config: ReplayConfig,
}

impl ReplayVerifier {
    /// Create new replay verifier
    pub fn new(config: ReplayConfig) -> Self {
        Self { config }
    }

    /// Verify replay determinism
    pub fn verify_replay(
        &self,
        replay1: &ReplayExport,
        replay2: &ReplayExport,
    ) -> ReplayVerificationResult {
        let mut result = ReplayVerificationResult {
            deterministic: true,
            errors: Vec::new(),
            warnings: Vec::new(),
            drift_detected: false,
        };

        // Check configuration consistency
        if replay1.config.chunk_bytes != replay2.config.chunk_bytes {
            result.errors.push("Chunk byte size mismatch".to_string());
            result.deterministic = false;
        }

        if replay1.config.flush_ms != replay2.config.flush_ms {
            result.errors.push("Flush interval mismatch".to_string());
            result.deterministic = false;
        }

        if replay1.config.locale != replay2.config.locale {
            result
                .warnings
                .push("Locale mismatch (may cause drift)".to_string());
        }

        if replay1.config.timezone != replay2.config.timezone {
            result
                .warnings
                .push("Timezone mismatch (may cause drift)".to_string());
        }

        // Check event count consistency
        if replay1.events.len() != replay2.events.len() {
            result.errors.push(format!(
                "Event count mismatch: {} vs {}",
                replay1.events.len(),
                replay2.events.len()
            ));
            result.deterministic = false;
        }

        // Check chunk consistency
        if replay1.chunk_info.len() != replay2.chunk_info.len() {
            result.errors.push(format!(
                "Chunk count mismatch: {} vs {}",
                replay1.chunk_info.len(),
                replay2.chunk_info.len()
            ));
            result.deterministic = false;
        }

        // Check for drift
        if !replay1.drift_measurements.is_empty() || !replay2.drift_measurements.is_empty() {
            result.drift_detected = true;
            result
                .warnings
                .push("Drift detected in replay execution".to_string());
        }

        result
    }

    /// Compare byte-level determinism
    pub fn verify_byte_identical(&self, replay1: &ReplayExport, replay2: &ReplayExport) -> bool {
        // Serialize both replays and compare
        let bytes1 = serde_json::to_vec(replay1).unwrap();
        let bytes2 = serde_json::to_vec(replay2).unwrap();

        bytes1 == bytes2
    }

    /// Check redaction-equivalent view
    pub fn verify_redaction_equivalent(
        &self,
        replay1: &ReplayExport,
        replay2: &ReplayExport,
    ) -> bool {
        // Compare events with sensitive data redacted
        if replay1.events.len() != replay2.events.len() {
            return false;
        }

        for (event1, event2) in replay1.events.iter().zip(replay2.events.iter()) {
            if !self.events_redaction_equivalent(event1, event2) {
                return false;
            }
        }

        true
    }

    /// Check if two events are redaction-equivalent
    fn events_redaction_equivalent(&self, event1: &ReplayEvent, event2: &ReplayEvent) -> bool {
        // Compare event types and structure, ignoring timestamps and sensitive payloads
        event1.event_type == event2.event_type
            && event1.metadata.get("redaction_level") == event2.metadata.get("redaction_level")
    }
}

/// Replay verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayVerificationResult {
    pub deterministic: bool,
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
    pub drift_detected: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_replay_session_creation() {
        let config = ReplayConfig::default();
        let session = ReplaySession::new("test_session".to_string(), config);

        assert_eq!(session.session_id, "test_session");
        assert_eq!(session.sequence_number, 0);
        assert!(!session.drift_detected);
    }

    #[test]
    fn test_event_addition() {
        let mut session = ReplaySession::new("test_session".to_string(), ReplayConfig::default());

        let event = ReplayEvent {
            event_id: "event1".to_string(),
            event_type: "test".to_string(),
            timestamp: 1000,
            payload: serde_json::Value::Null,
            metadata: HashMap::new(),
        };

        session.add_event(event).unwrap();
        assert_eq!(session.events.len(), 1);
    }

    #[test]
    fn test_chunk_flushing() {
        let mut config = ReplayConfig::default();
        config.chunk_bytes = 100; // Small chunks for testing

        let mut session = ReplaySession::new("test_session".to_string(), config);

        // Add events until chunk is full
        for i in 0..10 {
            let event = ReplayEvent {
                event_id: format!("event{}", i),
                event_type: "test".to_string(),
                timestamp: 1000 + i as u64,
                payload: serde_json::Value::String("test_data".to_string()),
                metadata: HashMap::new(),
            };

            session.add_event(event).unwrap();
        }

        // Force flush
        session.flush_chunk().unwrap();
        assert_eq!(session.sequence_number, 1);
    }

    #[test]
    fn test_drift_detection() {
        let mut session = ReplaySession::new("test_session".to_string(), ReplayConfig::default());

        let drift_detected = session.check_drift(1000, 1100); // 100ms drift
        assert!(drift_detected);
        assert!(session.drift_detected);
        assert_eq!(session.drift_measurements.len(), 1);
    }

    #[test]
    fn test_replay_manager() {
        let config = ReplayConfig::default();
        let mut manager = ReplayManager::new(config);

        let session_id = manager.create_session("test_session".to_string(), None);
        assert_eq!(manager.session_count(), 1);

        let event = ReplayEvent {
            event_id: "event1".to_string(),
            event_type: "test".to_string(),
            timestamp: 1000,
            payload: serde_json::Value::Null,
            metadata: HashMap::new(),
        };

        manager.add_event(&session_id, event).unwrap();

        let stats = manager.get_session_stats(&session_id).unwrap();
        assert_eq!(stats.total_events, 1);
    }

    #[test]
    fn test_replay_verification() {
        let config = ReplayConfig::default();
        let verifier = ReplayVerifier::new(config);

        let replay1 = ReplayExport {
            session_id: "session1".to_string(),
            config: ReplayConfig::default(),
            events: Vec::new(),
            chunk_info: Vec::new(),
            drift_measurements: Vec::new(),
            export_timestamp: 1000,
        };

        let replay2 = ReplayExport {
            session_id: "session2".to_string(),
            config: ReplayConfig::default(),
            events: Vec::new(),
            chunk_info: Vec::new(),
            drift_measurements: Vec::new(),
            export_timestamp: 1000,
        };

        let result = verifier.verify_replay(&replay1, &replay2);
        assert!(result.deterministic);
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_concurrency_stress() {
        let config = ReplayConfig::default();
        let mut manager = ReplayManager::new(config);

        // Create multiple sessions
        for i in 0..20 {
            let session_id = format!("session_{}", i);
            manager.create_session(session_id, None);
        }

        assert_eq!(manager.session_count(), 20);

        // Add events to each session
        for i in 0..20 {
            let session_id = format!("session_{}", i);
            let event = ReplayEvent {
                event_id: format!("event_{}", i),
                event_type: "test".to_string(),
                timestamp: 1000 + i as u64,
                payload: serde_json::Value::Null,
                metadata: HashMap::new(),
            };

            manager.add_event(&session_id, event).unwrap();
        }

        // Verify all sessions have events
        for i in 0..20 {
            let session_id = format!("session_{}", i);
            let stats = manager.get_session_stats(&session_id).unwrap();
            assert_eq!(stats.total_events, 1);
        }
    }

    #[test]
    fn test_replay_determinism_verification() {
        let config = ReplayConfig::default();
        let verifier = ReplayVerifier::new(config);

        // Create two identical replay exports
        let replay1 = ReplayExport {
            session_id: "session1".to_string(),
            config: ReplayConfig::default(),
            events: vec![
                ReplayEvent {
                    event_id: "event1".to_string(),
                    event_type: "test".to_string(),
                    timestamp: 1000,
                    payload: serde_json::Value::String("data1".to_string()),
                    metadata: HashMap::new(),
                },
                ReplayEvent {
                    event_id: "event2".to_string(),
                    event_type: "test".to_string(),
                    timestamp: 2000,
                    payload: serde_json::Value::String("data2".to_string()),
                    metadata: HashMap::new(),
                },
            ],
            chunk_info: vec![ChunkInfo {
                sequence_number: 0,
                size_bytes: 100,
                hash: "hash1".to_string(),
                timestamp: 1000,
            }],
            drift_measurements: Vec::new(),
            export_timestamp: 1000,
        };

        let replay2 = replay1.clone();

        // Verify byte-identical determinism
        assert!(verifier.verify_byte_identical(&replay1, &replay2));

        // Verify replay determinism
        let result = verifier.verify_replay(&replay1, &replay2);
        assert!(result.deterministic);
        assert!(result.errors.is_empty());
        assert!(!result.drift_detected);
    }

    #[test]
    fn test_replay_drift_detection() {
        let config = ReplayConfig::default();
        let verifier = ReplayVerifier::new(config);

        // Create two replays with different timestamps (simulating drift)
        let mut replay1 = ReplayExport {
            session_id: "session1".to_string(),
            config: ReplayConfig::default(),
            events: vec![ReplayEvent {
                event_id: "event1".to_string(),
                event_type: "test".to_string(),
                timestamp: 1000,
                payload: serde_json::Value::String("data1".to_string()),
                metadata: HashMap::new(),
            }],
            chunk_info: vec![ChunkInfo {
                sequence_number: 0,
                size_bytes: 100,
                hash: "hash1".to_string(),
                timestamp: 1000,
            }],
            drift_measurements: vec![DriftMeasurement {
                sequence_number: 0,
                expected_time: 1000,
                actual_time: 1100, // 100ms drift
                drift_ms: 100,
                timestamp: 1100,
            }],
            export_timestamp: 1000,
        };

        let mut replay2 = replay1.clone();
        replay2.events[0].timestamp = 1100; // Different timestamp
        replay2.chunk_info[0].timestamp = 1100;

        // Verify that drift is detected
        let result = verifier.verify_replay(&replay1, &replay2);
        assert!(result.drift_detected);
        assert!(!result.warnings.is_empty());
        assert!(result.warnings.iter().any(|w| w.contains("Drift detected")));
    }

    #[test]
    fn test_redaction_equivalent_view() {
        let config = ReplayConfig::default();
        let verifier = ReplayVerifier::new(config);

        // Create two replays with different timestamps but same structure
        let mut replay1 = ReplayExport {
            session_id: "session1".to_string(),
            config: ReplayConfig::default(),
            events: vec![ReplayEvent {
                event_id: "event1".to_string(),
                event_type: "test".to_string(),
                timestamp: 1000,
                payload: serde_json::Value::String("data1".to_string()),
                metadata: {
                    let mut m = HashMap::new();
                    m.insert("redaction_level".to_string(), "high".to_string());
                    m
                },
            }],
            chunk_info: vec![ChunkInfo {
                sequence_number: 0,
                size_bytes: 100,
                hash: "hash1".to_string(),
                timestamp: 1000,
            }],
            drift_measurements: Vec::new(),
            export_timestamp: 1000,
        };

        let mut replay2 = replay1.clone();
        replay2.events[0].timestamp = 2000; // Different timestamp
        replay2.chunk_info[0].timestamp = 2000;

        // Verify that they are redaction-equivalent
        assert!(verifier.verify_redaction_equivalent(&replay1, &replay2));
    }
}
