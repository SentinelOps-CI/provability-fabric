// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 SentinelOps Platform Contributors

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::VecDeque;
use std::time::{Duration, Instant};
use tracing::debug;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressProfile {
    pub name: String,
    pub version: String,
    pub chunk_size: usize,
    pub flush_cadence_ms: u64,
    pub locale: String,
    pub timezone: String,
    pub padding_policy: PaddingPolicy,
    pub seed: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PaddingPolicy {
    Fixed { size: usize },
    Random { min: usize, max: usize },
    None,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EgressEvent {
    pub session_id: String,
    pub sequence: u64,
    pub data: Vec<u8>,
    pub timestamp: u64,
    pub chunk_hash: String,
    pub metadata: std::collections::HashMap<String, String>,
}

pub struct EgressManager {
    profile: EgressProfile,
    buffer: VecDeque<u8>,
    sequence_counter: u64,
    last_flush: Instant,
    session_id: String,
    pending_events: Vec<EgressEvent>,
}

impl Default for EgressProfile {
    fn default() -> Self {
        Self {
            name: "EGRESS-DET-P1".to_string(),
            version: "1.0".to_string(),
            chunk_size: 4096,
            flush_cadence_ms: 100,
            locale: "C".to_string(),
            timezone: "UTC".to_string(),
            padding_policy: PaddingPolicy::Fixed { size: 4096 },
            seed: 42,
        }
    }
}

impl EgressManager {
    pub fn new(profile: EgressProfile, session_id: String) -> Self {
        // Set deterministic environment
        std::env::set_var("LC_ALL", &profile.locale);
        std::env::set_var("TZ", &profile.timezone);

        Self {
            profile,
            buffer: VecDeque::new(),
            sequence_counter: 0,
            last_flush: Instant::now(),
            session_id,
            pending_events: Vec::new(),
        }
    }

    pub async fn write_egress(&mut self, data: &[u8]) -> Result<Vec<EgressEvent>> {
        // Add data to buffer
        self.buffer.extend(data);

        let mut events = Vec::new();

        // Process complete chunks
        while self.buffer.len() >= self.profile.chunk_size {
            let chunk = self.extract_chunk();
            let event = self.create_egress_event(chunk)?;
            events.push(event);
        }

        // Check if flush cadence requires flushing remaining data
        if self.should_flush() {
            if !self.buffer.is_empty() {
                let chunk = self.extract_remaining_chunk();
                let event = self.create_egress_event(chunk)?;
                events.push(event);
            }
            self.last_flush = Instant::now();
        }

        // Store pending events
        self.pending_events.extend(events.clone());

        Ok(events)
    }

    pub async fn flush_all(&mut self) -> Result<Vec<EgressEvent>> {
        let mut events = Vec::new();

        // Flush any remaining data
        if !self.buffer.is_empty() {
            let chunk = self.extract_remaining_chunk();
            let event = self.create_egress_event(chunk)?;
            events.push(event);
        }

        // Return all pending events
        events.append(&mut self.pending_events);

        Ok(events)
    }

    fn extract_chunk(&mut self) -> Vec<u8> {
        let mut chunk = vec![0u8; self.profile.chunk_size];
        for slot in &mut chunk {
            if let Some(byte) = self.buffer.pop_front() {
                *slot = byte;
            }
        }
        chunk
    }

    fn extract_remaining_chunk(&mut self) -> Vec<u8> {
        let _remaining_size = self.buffer.len();
        let mut chunk: Vec<u8> = self.buffer.drain(..).collect();

        // Apply padding policy
        match &self.profile.padding_policy {
            PaddingPolicy::Fixed { size } => {
                if chunk.len() < *size {
                    chunk.resize(*size, 0);
                }
            }
            PaddingPolicy::Random { min, max } => {
                let target_size = (*min + (*max - *min) * (self.profile.seed as usize % 100) / 100)
                    .max(chunk.len());
                if chunk.len() < target_size {
                    chunk.resize(target_size, 0);
                }
            }
            PaddingPolicy::None => {
                // No padding
            }
        }

        chunk
    }

    fn create_egress_event(&mut self, chunk: Vec<u8>) -> Result<EgressEvent> {
        self.sequence_counter += 1;

        // Calculate deterministic chunk hash
        let chunk_hash = self.calculate_chunk_hash(&chunk);

        let event = EgressEvent {
            session_id: self.session_id.clone(),
            sequence: self.sequence_counter,
            data: chunk,
            timestamp: sidecar_watcher::time_util::unix_secs(),
            chunk_hash,
            metadata: std::collections::HashMap::new(),
        };

        debug!(
            "Created egress event: session={}, seq={}, size={}",
            event.session_id,
            event.sequence,
            event.data.len()
        );

        Ok(event)
    }

    fn should_flush(&self) -> bool {
        self.last_flush.elapsed() >= Duration::from_millis(self.profile.flush_cadence_ms)
    }

    fn calculate_chunk_hash(&self, chunk: &[u8]) -> String {
        // Deterministic hash calculation
        use sha2::{Digest, Sha256};
        let mut hasher = Sha256::new();
        hasher.update(chunk);
        hasher.update(self.session_id.as_bytes());
        hasher.update(self.sequence_counter.to_le_bytes());
        hasher.update(self.profile.seed.to_le_bytes());

        format!("{:x}", hasher.finalize())
    }

    pub fn get_profile(&self) -> &EgressProfile {
        &self.profile
    }

    pub fn get_stats(&self) -> EgressStats {
        EgressStats {
            total_events: self.sequence_counter,
            buffer_size: self.buffer.len(),
            pending_events: self.pending_events.len(),
            last_flush_ms: self.last_flush.elapsed().as_millis() as u64,
        }
    }
}

#[derive(Debug, Serialize)]
pub struct EgressStats {
    pub total_events: u64,
    pub buffer_size: usize,
    pub pending_events: usize,
    pub last_flush_ms: u64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_egress_manager_chunks() {
        let profile = EgressProfile::default();
        let mut manager = EgressManager::new(profile, "session-1".to_string());
        let events = manager.write_egress(b"hello world").await.unwrap();
        assert!(!events.is_empty());
        let stats = manager.get_stats();
        assert!(stats.total_events >= 1);
        assert_eq!(manager.get_profile().name, "EGRESS-DET-P1");
    }
}
