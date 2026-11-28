/*
 * SPDX-License-Identifier: Apache-2.0
 * Copyright 2025 Provability-Fabric Contributors
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * you may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::time::{SystemTime, UNIX_EPOCH};

// Length framing prevents ambiguous concatenations of adjacent fields.
fn hash_field(hasher: &mut Sha256, value: &[u8]) {
    hasher.update((value.len() as u64).to_be_bytes());
    hasher.update(value);
}

fn hash_strings(hasher: &mut Sha256, values: &[String]) {
    hasher.update((values.len() as u64).to_be_bytes());
    for value in values {
        hash_field(hasher, value.as_bytes());
    }
}

fn hash_labels(hasher: &mut Sha256, labels: &[SecurityLabel]) {
    hasher.update((labels.len() as u64).to_be_bytes());
    for label in labels {
        hash_field(hasher, label.to_string().as_bytes());
    }
}

fn unix_timestamp_secs() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

/// Non-interference monitor configuration
///
/// This monitor implements the \MonNI_L definition from the formal specification.
/// The monitor ensures that low-level views coincide across all prefixes,
/// providing the local component of the global non-interference guarantee.
///
/// \MonNI_L requires:
/// 1. All prefixes respect label ordering (input_label ≤ output_label)
/// 2. No non-interference violations in strict mode
/// 3. Monitor state consistency and audit trail
/// 4. Proof hash verification for bridge guarantees
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIMonitorConfig {
    pub enable_monitoring: bool,
    pub strict_mode: bool,
    pub max_prefixes: usize,
    pub prefix_length: usize,
    pub drift_threshold_ms: u64,
    pub enable_audit_logging: bool,
    pub proof_hash_verification: bool, // New: enable proof hash verification
    pub automata_hash_verification: bool, // New: enable automata hash verification
    pub labeler_hash_verification: bool, // New: enable labeler hash verification
}

impl Default for NIMonitorConfig {
    fn default() -> Self {
        Self {
            enable_monitoring: true,
            strict_mode: true,
            max_prefixes: 10000,
            prefix_length: 64,
            drift_threshold_ms: 100,
            enable_audit_logging: true,
            proof_hash_verification: true,
            automata_hash_verification: true,
            labeler_hash_verification: true,
        }
    }
}

/// Security label for non-interference analysis
///
/// Labels follow the lattice ordering defined in the formal specification.
/// The \MonNI_L monitor uses these labels to determine information flow.
///
/// Lattice ordering: Public ≤ Internal ≤ Confidential ≤ Secret
/// Custom labels require explicit declassification rules.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SecurityLabel {
    Public,
    Internal,
    Confidential,
    Secret,
    Custom(String),
}

impl fmt::Display for SecurityLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SecurityLabel::Public => f.write_str("public"),
            SecurityLabel::Internal => f.write_str("internal"),
            SecurityLabel::Confidential => f.write_str("confidential"),
            SecurityLabel::Secret => f.write_str("secret"),
            SecurityLabel::Custom(name) => write!(f, "custom:{name}"),
        }
    }
}

impl SecurityLabel {
    /// Parse from string representation
    pub fn from_string(s: &str) -> Result<Self, String> {
        match s {
            "public" => Ok(SecurityLabel::Public),
            "internal" => Ok(SecurityLabel::Internal),
            "confidential" => Ok(SecurityLabel::Confidential),
            "secret" => Ok(SecurityLabel::Secret),
            s if s.starts_with("custom:") => {
                let name = s
                    .strip_prefix("custom:")
                    .ok_or_else(|| format!("Invalid custom label prefix: {}", s))?;
                Ok(SecurityLabel::Custom(name.to_string()))
            }
            _ => Err(format!("Unknown security label: {}", s)),
        }
    }

    /// Check if this label is less than or equal to another (lattice ordering)
    ///
    /// This implements the exact ordering required by \MonNI_L:
    /// Public ≤ Internal ≤ Confidential ≤ Secret
    /// Custom labels only equal themselves
    pub fn le(&self, other: &SecurityLabel) -> bool {
        match (self, other) {
            (SecurityLabel::Public, _) => true,
            (SecurityLabel::Internal, SecurityLabel::Internal) => true,
            (SecurityLabel::Internal, SecurityLabel::Confidential) => true,
            (SecurityLabel::Internal, SecurityLabel::Secret) => true,
            (SecurityLabel::Confidential, SecurityLabel::Confidential) => true,
            (SecurityLabel::Confidential, SecurityLabel::Secret) => true,
            (SecurityLabel::Secret, SecurityLabel::Secret) => true,
            (SecurityLabel::Custom(name1), SecurityLabel::Custom(name2)) => name1 == name2,
            _ => false,
        }
    }

    /// Check if this label is greater than or equal to another
    pub fn ge(&self, other: &SecurityLabel) -> bool {
        other.le(self)
    }
}

/// Event for non-interference analysis
///
/// Each event represents an operation that must respect non-interference constraints.
/// The \MonNI_L monitor tracks these events to ensure label flow compliance.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIEvent {
    pub event_id: String,
    pub timestamp: u64,
    pub session_id: String,
    pub user_id: String,
    pub operation: String,
    pub input_labels: Vec<SecurityLabel>,
    pub output_labels: Vec<SecurityLabel>,
    pub data_paths: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// Prefix for non-interference analysis
///
/// A prefix represents a sequence of events that must maintain non-interference.
/// The \MonNI_L monitor ensures that all prefixes respect the security policy.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIPrefix {
    pub prefix_id: String,
    pub events: Vec<NIEvent>,
    pub input_label: SecurityLabel,
    pub output_label: SecurityLabel,
    pub created_at: u64,
    pub last_updated: u64,
}

impl NIPrefix {
    /// Create new NI prefix
    pub fn new(prefix_id: String, input_label: SecurityLabel, output_label: SecurityLabel) -> Self {
        let now = unix_timestamp_secs();

        Self {
            prefix_id,
            events: Vec::new(),
            input_label,
            output_label,
            created_at: now,
            last_updated: now,
        }
    }

    /// Add event to prefix
    pub fn add_event(&mut self, event: NIEvent) {
        self.events.push(event);
        self.last_updated = unix_timestamp_secs();
    }

    /// Check if prefix violates non-interference
    ///
    /// This implements the exact violation detection logic required by \MonNI_L:
    /// 1. Every observed input flows only to an equal or higher output label.
    /// 2. Every input and output respects the declared prefix bounds.
    ///
    /// This is a local label-flow check, not a proof of global noninterference.
    pub fn violates_ni(&self) -> bool {
        for event in &self.events {
            if event.input_labels.is_empty() || event.output_labels.is_empty()
                || event.input_labels.iter().any(|input|
                    event.output_labels.iter().any(|output| !input.le(output)))
            {
                return true;
            }
        }
        // Check if any event has input labels that are not dominated by the prefix input label
        for event in &self.events {
            for input_label in &event.input_labels {
                if !input_label.le(&self.input_label) {
                    return true;
                }
            }
        }

        // Check if any event has output labels that dominate the prefix output label
        for event in &self.events {
            for output_label in &event.output_labels {
                if !self.output_label.le(output_label) {
                    return true;
                }
            }
        }

        false
    }

    /// Get prefix hash for verification
    ///
    /// This hash is used to verify prefix integrity and is included in certificates
    /// to provide cryptographic proof of the prefix state.
    pub fn get_hash(&self) -> String {
        let mut hasher = Sha256::new();
        hash_field(&mut hasher, b"pf-ni-prefix-v2");
        hash_field(&mut hasher, self.prefix_id.as_bytes());
        hash_field(&mut hasher, self.input_label.to_string().as_bytes());
        hash_field(&mut hasher, self.output_label.to_string().as_bytes());
        hasher.update(self.created_at.to_be_bytes());
        hasher.update(self.last_updated.to_be_bytes());
        hasher.update((self.events.len() as u64).to_be_bytes());

        for event in &self.events {
            hash_field(&mut hasher, event.event_id.as_bytes());
            hasher.update(event.timestamp.to_be_bytes());
            hash_field(&mut hasher, event.session_id.as_bytes());
            hash_field(&mut hasher, event.user_id.as_bytes());
            hash_field(&mut hasher, event.operation.as_bytes());
            hash_labels(&mut hasher, &event.input_labels);
            hash_labels(&mut hasher, &event.output_labels);
            hash_strings(&mut hasher, &event.data_paths);
            let mut metadata: Vec<_> = event.metadata.iter().collect();
            metadata.sort_unstable_by(|a, b| a.0.cmp(b.0));
            hasher.update((metadata.len() as u64).to_be_bytes());
            for (key, value) in metadata {
                hash_field(&mut hasher, key.as_bytes());
                hash_field(&mut hasher, value.as_bytes());
            }
        }

        format!("{:x}", hasher.finalize())
    }
}

/// Proof hashes for certificate integrity
///
/// These hashes ensure that the runtime implementation matches the formal proofs
/// and provide cryptographic verification of the system's correctness.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofHashes {
    pub policy_proof_hash: String, // SHA-256 of Policy.lean
    pub automata_hash: String,     // SHA-256 of generated DFA
    pub labeler_hash: String,      // SHA-256 of label derivation logic
    pub ni_bridge_hash: String,    // SHA-256 of ni_bridge theorem
    pub computed_at: u64,
}

impl Default for ProofHashes {
    fn default() -> Self {
        Self::new()
    }
}

impl ProofHashes {
    /// Create new proof hashes
    pub fn new() -> Self {
        let now = unix_timestamp_secs();

        Self {
            policy_proof_hash: String::new(),
            automata_hash: String::new(),
            labeler_hash: String::new(),
            ni_bridge_hash: String::new(),
            computed_at: now,
        }
    }

    /// Compute proof hashes from file contents
    pub fn compute_from_files(
        &mut self,
        policy_content: &str,
        automata_content: &str,
        labeler_content: &str,
    ) {
        let mut hasher = Sha256::new();
        hasher.update(policy_content.as_bytes());
        self.policy_proof_hash = format!("{:x}", hasher.finalize());

        let mut hasher = Sha256::new();
        hasher.update(automata_content.as_bytes());
        self.automata_hash = format!("{:x}", hasher.finalize());

        let mut hasher = Sha256::new();
        hasher.update(labeler_content.as_bytes());
        self.labeler_hash = format!("{:x}", hasher.finalize());

        // Compute hash of the ni_bridge theorem specifically
        let ni_bridge_content = "theorem ni_bridge : ∀ (u : Principal) (a : Action) (γ : Ctx) (monitor : NIMonitor) (prefixes : List NIPrefix), permitD u a γ = true → (∀ prefix ∈ prefixes, monitor.accepts_prefix prefix) → GlobalNonInterference monitor prefixes";
        let mut hasher = Sha256::new();
        hasher.update(ni_bridge_content.as_bytes());
        self.ni_bridge_hash = format!("{:x}", hasher.finalize());

        self.computed_at = unix_timestamp_secs();
    }

    /// Verify that proof hashes match expected values
    pub fn verify_hashes(&self, expected_hashes: &ProofHashes) -> bool {
        self.policy_proof_hash == expected_hashes.policy_proof_hash
            && self.automata_hash == expected_hashes.automata_hash
            && self.labeler_hash == expected_hashes.labeler_hash
            && self.ni_bridge_hash == expected_hashes.ni_bridge_hash
    }
}

/// Non-interference monitor state
///
/// This state maintains the monitor's internal state and ensures consistency
/// with the \MonNI_L formal specification requirements.
#[derive(Debug, Clone)]
pub struct NIMonitorState {
    pub prefixes: HashMap<String, NIPrefix>,
    // Local process-memory reference only; not an external attestation.
    prefix_digests: HashMap<String, String>,
    pub active_sessions: HashSet<String>,
    pub violation_count: u64,
    pub last_audit: u64,
    pub config: NIMonitorConfig,
    pub proof_hashes: ProofHashes, // New: proof hashes for verification
}

impl NIMonitorState {
    /// Create new NI monitor state
    pub fn new(config: NIMonitorConfig) -> Self {
        Self {
            prefixes: HashMap::new(),
            prefix_digests: HashMap::new(),
            active_sessions: HashSet::new(),
            violation_count: 0,
            last_audit: unix_timestamp_secs(),
            config,
            proof_hashes: ProofHashes::new(),
        }
    }

    /// Add event to monitor
    ///
    /// This method implements the exact event processing logic required by \MonNI_L.
    /// It ensures that all events respect non-interference constraints and maintains
    /// the monitor's internal consistency.
    pub fn add_event(&mut self, event: NIEvent) -> Result<bool, String> {
        if !self.config.enable_monitoring {
            return Ok(true);
        }

        // Validate the slicing boundary before constructing a prefix ID.
        if !(8..=71).contains(&self.config.prefix_length) {
            return Err("Invalid NI prefix length".to_string());
        }
        let prefix_id = self.generate_prefix_id(&event);

        // Existing prefixes do not consume an additional prefix slot.
        if !self.prefixes.contains_key(&prefix_id)
            && self.prefixes.len() >= self.config.max_prefixes
        {
            return Err("Maximum number of prefixes exceeded".to_string());
        }

        // Detect unexpected state changes before extending the prefix.
        if self.prefixes.contains_key(&prefix_id) && !self.verify_prefix_integrity(&prefix_id)? {
            return Err("NI prefix integrity mismatch".to_string());
        }

        // Get or create prefix, add event, and evaluate violations in one pass.
        let (violates, audit_prefix, digest) = {
            let prefix = self.prefixes.entry(prefix_id.clone()).or_insert_with(|| {
                NIPrefix::new(
                    prefix_id.clone(),
                    event
                        .input_labels
                        .first()
                        .unwrap_or(&SecurityLabel::Public)
                        .clone(),
                    event
                        .output_labels
                        .first()
                        .unwrap_or(&SecurityLabel::Public)
                        .clone(),
                )
            });

            prefix.add_event(event.clone());
            let violates = prefix.violates_ni();
            let audit_prefix = if self.config.enable_audit_logging {
                Some(prefix.clone())
            } else {
                None
            };
            (violates, audit_prefix, prefix.get_hash())
        };
        self.prefix_digests.insert(prefix_id, digest);

        if violates {
            self.violation_count += 1;
        }

        // Record denied attempts as well as accepted attempts.
        if let Some(prefix_clone) = audit_prefix {
            self.log_audit_event(&event, &prefix_clone);
        }
        if violates && self.config.strict_mode {
            return Err("Non-interference violation detected".to_string());
        }

        self.active_sessions.insert(event.session_id.clone());
        Ok(true)
    }

    /// Generate prefix ID for an event
    fn generate_prefix_id(&self, event: &NIEvent) -> String {
        let mut hasher = Sha256::new();
        hasher.update(event.session_id.as_bytes());
        hasher.update(event.operation.as_bytes());

        // Include input and output labels in prefix ID
        for label in &event.input_labels {
            hasher.update(label.to_string().as_bytes());
        }
        for label in &event.output_labels {
            hasher.update(label.to_string().as_bytes());
        }

        let hash = hasher.finalize();
        format!("prefix_{:x}", hash)[..self.config.prefix_length].to_string()
    }

    /// Log audit event
    fn log_audit_event(&mut self, event: &NIEvent, prefix: &NIPrefix) {
        let now = unix_timestamp_secs();

        // Log to audit trail (in a real implementation, this would go to a secure log)
        println!(
            "[AUDIT] {} - Session: {}, User: {}, Operation: {}, Prefix: {}, Violation: {}",
            now,
            event.session_id,
            event.user_id,
            event.operation,
            prefix.prefix_id,
            prefix.violates_ni()
        );

        self.last_audit = now;
    }

    /// Check all prefixes for violations
    pub fn check_all_prefixes(&self) -> Vec<String> {
        let mut violations = Vec::new();

        for prefix in self.prefixes.values() {
            if prefix.violates_ni() {
                violations.push(format!(
                    "Prefix {} violates non-interference: input={}, output={}",
                    prefix.prefix_id, prefix.input_label, prefix.output_label
                ));
            }
        }

        violations
    }

    /// Get monitor statistics
    pub fn get_stats(&self) -> NIMonitorStats {
        NIMonitorStats {
            total_prefixes: self.prefixes.len(),
            active_sessions: self.active_sessions.len(),
            violation_count: self.violation_count,
            last_audit: self.last_audit,
            config: self.config.clone(),
            proof_hashes: self.proof_hashes.clone(),
        }
    }

    /// Generate bridge guarantee for the current monitor state
    ///
    /// This method provides the local component of the global non-interference claim.
    /// It ensures that the runtime's local checks match the proof preconditions
    /// required by Theorem ni-bridge.
    ///
    /// The bridge guarantee is the key component that connects local runtime checks
    /// to the global non-interference properties proven in the formal specification.
    pub fn generate_bridge_guarantee(&self) -> BridgeGuarantee {
        let local_checks_ok = self.check_bridge_conditions();
        let proof_verification = self.verify_proof_hashes();

        BridgeGuarantee {
            theorem_reference: "ni-bridge".to_string(),
            local_checks_ok,
            global_ni_claim: "global_non_interference".to_string(),
            proof_verification,
            bridge_conditions: self.get_bridge_conditions(),
            proof_hashes: self.proof_hashes.clone(),
        }
    }

    /// Check if all bridge conditions are satisfied
    ///
    /// These conditions must hold for the bridge guarantee to be valid.
    /// They ensure that the runtime implementation matches the formal proof.
    fn check_bridge_conditions(&self) -> bool {
        // Condition 1: All prefixes respect the label ordering
        let label_ordering_ok = self
            .prefixes
            .iter()
            .all(|(_name, prefix)| prefix.input_label.le(&prefix.output_label));

        // Condition 2: No violations in strict mode
        let no_violations = self.violation_count == 0 || !self.config.strict_mode;

        // Condition 3: Monitor state is consistent
        let state_consistent = self.last_audit > 0 && !self.active_sessions.is_empty();

        // Condition 4: Proof hashes are available
        let prefix_integrity_ok = self.prefixes.keys().all(|id|
            self.verify_prefix_integrity(id).unwrap_or(false));

        label_ordering_ok && no_violations && state_consistent && prefix_integrity_ok
            && self.verify_proof_hashes()
    }

    /// Verify that proof hashes match expected values
    ///
    /// This verification ensures that the runtime implementation matches
    /// the formal proofs and generated artifacts.
    fn verify_proof_hashes(&self) -> bool {
        // No independently trusted artifact manifest is wired into this monitor.
        // Nonempty or locally generated hashes, and disabled verification, do
        // not establish correspondence with a reviewed proof or executable.
        false
    }

    /// Get the list of bridge conditions that must hold
    fn get_bridge_conditions(&self) -> Vec<String> {
        vec![
            "All prefixes respect label ordering".to_string(),
            "No non-interference violations".to_string(),
            "Monitor state is consistent".to_string(),
            "Proof hashes match expected values".to_string(),
            "Automata hashes verified".to_string(),
            "Labeler hashes verified".to_string(),
            "NI bridge theorem hash verified".to_string(),
        ]
    }

    /// Clean up old prefixes
    pub fn cleanup_old_prefixes(&mut self, max_age_seconds: u64) {
        let now = unix_timestamp_secs();

        let mut to_remove = Vec::new();

        for (prefix_id, prefix) in &self.prefixes {
            if now.saturating_sub(prefix.last_updated) > max_age_seconds {
                to_remove.push(prefix_id.clone());
            }
        }

        for prefix_id in to_remove {
            self.prefixes.remove(&prefix_id);
            self.prefix_digests.remove(&prefix_id);
        }
    }

    /// Verify prefix integrity
    pub fn verify_prefix_integrity(&self, prefix_id: &str) -> Result<bool, String> {
        let prefix = self
            .prefixes
            .get(prefix_id)
            .ok_or_else(|| format!("Prefix {} not found", prefix_id))?;

        let computed_hash = prefix.get_hash();

        let expected = self.prefix_digests.get(prefix_id)
            .ok_or_else(|| format!("No recorded digest for prefix {prefix_id}"))?;
        Ok(&computed_hash == expected)
    }

    /// Update proof hashes
    ///
    /// This method allows the monitor to update its proof hashes when
    /// new proofs are built or artifacts are generated.
    pub fn update_proof_hashes(&mut self, new_hashes: ProofHashes) {
        self.proof_hashes = new_hashes;
    }
}

/// Non-interference monitor statistics
///
/// These statistics provide operational insights into the monitor's behavior
/// and help verify that it's operating correctly according to the \MonNI_L specification.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIMonitorStats {
    pub total_prefixes: usize,
    pub active_sessions: usize,
    pub violation_count: u64,
    pub last_audit: u64,
    pub config: NIMonitorConfig,
    pub proof_hashes: ProofHashes, // New: include proof hashes in stats
}

/// Bridge guarantee linking local checks to global NI claims
///
/// This structure provides the formal connection between runtime checks and
/// the global non-interference properties proven in the formal specification.
/// It is the key component that enables auditors to verify that the runtime
/// implementation correctly implements the proven security properties.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BridgeGuarantee {
    pub theorem_reference: String,
    pub local_checks_ok: bool,
    pub global_ni_claim: String,
    pub proof_verification: bool,
    pub bridge_conditions: Vec<String>,
    pub proof_hashes: ProofHashes, // New: include proof hashes in guarantee
}

/// Non-interference monitor
///
/// This is the main monitor implementation that enforces the \MonNI_L specification.
/// It ensures that all operations respect non-interference constraints and maintains
/// the bridge guarantee connecting local checks to global security properties.
pub struct NIMonitor {
    state: NIMonitorState,
}

impl NIMonitor {
    /// Create new NI monitor
    pub fn new(config: NIMonitorConfig) -> Self {
        Self {
            state: NIMonitorState::new(config),
        }
    }

    /// Monitor an event for non-interference violations
    ///
    /// This method implements the core monitoring logic required by \MonNI_L.
    /// It processes each event and ensures that it respects non-interference constraints.
    pub fn monitor_event(&mut self, event: NIEvent) -> Result<bool, String> {
        self.state.add_event(event)
    }

    /// Track MonNI predicate online and emit ni_monitor status
    ///
    /// This method implements the local monitor to global NI bridge by tracking
    /// the MonNI_L predicate online and emitting accept|reject|inapplicable status
    /// for each input prefix. This provides the runtime component of the bridge
    /// that connects to the global non-interference properties proven offline.
    pub fn track_monni_online(&mut self, prefix: &NIPrefix) -> NIMonitorStatus {
        // Check if prefix violates non-interference
        if prefix.violates_ni() {
            self.state.violation_count += 1;
            return NIMonitorStatus::Reject;
        }

        // Check if prefix is inapplicable (no events or invalid state)
        if prefix.events.is_empty() {
            return NIMonitorStatus::Inapplicable;
        }

        // Check if all bridge conditions are satisfied
        if !self.state.check_bridge_conditions() {
            return NIMonitorStatus::Reject;
        }

        // If all checks pass, the prefix is accepted
        NIMonitorStatus::Accept
    }

    /// Get current MonNI status for all prefixes
    ///
    /// This method provides the current status of the MonNI_L predicate for all
    /// tracked prefixes, enabling the runtime to emit ni_monitor statuses as
    /// required by the bridge theorem.
    pub fn get_monni_status(&self) -> HashMap<String, NIMonitorStatus> {
        let mut statuses = HashMap::new();

        for (prefix_id, prefix) in &self.state.prefixes {
            let status = if prefix.violates_ni() {
                NIMonitorStatus::Reject
            } else if prefix.events.is_empty() {
                NIMonitorStatus::Inapplicable
            } else if self.state.check_bridge_conditions() {
                NIMonitorStatus::Accept
            } else {
                NIMonitorStatus::Reject
            };

            statuses.insert(prefix_id.clone(), status);
        }

        statuses
    }

    /// Check all prefixes for violations
    pub fn check_violations(&self) -> Vec<String> {
        self.state.check_all_prefixes()
    }

    /// Get monitor statistics
    pub fn get_stats(&self) -> NIMonitorStats {
        self.state.get_stats()
    }

    /// Clean up old prefixes
    pub fn cleanup(&mut self, max_age_seconds: u64) {
        self.state.cleanup_old_prefixes(max_age_seconds);
    }

    /// Verify prefix integrity
    pub fn verify_prefix(&self, prefix_id: &str) -> Result<bool, String> {
        self.state.verify_prefix_integrity(prefix_id)
    }

    /// Get all prefixes
    pub fn get_prefixes(&self) -> &HashMap<String, NIPrefix> {
        &self.state.prefixes
    }

    /// Get specific prefix
    pub fn get_prefix(&self, prefix_id: &str) -> Option<&NIPrefix> {
        self.state.prefixes.get(prefix_id)
    }

    /// Generate bridge guarantee
    ///
    /// This method generates the bridge guarantee that connects local runtime checks
    /// to the global non-interference properties proven in the formal specification.
    /// It is the key component that enables auditors to verify system correctness.
    pub fn generate_bridge_guarantee(&self) -> BridgeGuarantee {
        self.state.generate_bridge_guarantee()
    }

    /// Update proof hashes
    ///
    /// This method allows the monitor to update its proof hashes when
    /// new proofs are built or artifacts are generated.
    pub fn update_proof_hashes(&mut self, new_hashes: ProofHashes) {
        self.state.update_proof_hashes(new_hashes);
    }
}

/// Non-interference proof obligation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIProofObligation {
    pub obligation_id: String,
    pub prefix_id: String,
    pub condition: String,
    pub proof: String,
    pub verified: bool,
    pub verified_at: Option<u64>,
}

/// Non-interference verification result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NIVerificationResult {
    pub prefix_id: String,
    pub verified: bool,
    pub violations: Vec<String>,
    pub proof_obligations: Vec<NIProofObligation>,
    pub timestamp: u64,
}

/// MonNI monitor status for each prefix
///
/// This enum represents the possible states of the MonNI_L predicate
/// as tracked online by the runtime monitor.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum NIMonitorStatus {
    Accept,
    Reject,
    Inapplicable,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn test_security_label_ordering() {
        assert!(SecurityLabel::Public.le(&SecurityLabel::Secret));
        assert!(SecurityLabel::Internal.le(&SecurityLabel::Confidential));
        assert!(!SecurityLabel::Secret.le(&SecurityLabel::Public));
    }

    #[test]
    fn test_ni_prefix_creation() {
        let prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Confidential,
            SecurityLabel::Internal,
        );

        assert_eq!(prefix.prefix_id, "test_prefix");
        assert_eq!(prefix.events.len(), 0);
        assert!(!prefix.violates_ni());
    }

    #[test]
    fn test_ni_prefix_violation() {
        let mut prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Internal,
            SecurityLabel::Confidential,
        );

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Secret], // Higher than prefix input
            output_labels: vec![SecurityLabel::Internal],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        prefix.add_event(event);
        assert!(prefix.violates_ni());
    }

    #[test]
    fn test_local_flow_rejects_missing_and_mixed_labels() {
        let mut monitor = NIMonitor::new(NIMonitorConfig::default());
        let event = NIEvent {
            event_id: "mixed".into(),
            timestamp: 1000,
            session_id: "session".into(),
            user_id: "user".into(),
            operation: "read".into(),
            input_labels: vec![SecurityLabel::Public, SecurityLabel::Secret],
            output_labels: vec![SecurityLabel::Public, SecurityLabel::Secret],
            data_paths: vec!["$.data".into()],
            metadata: HashMap::new(),
        };
        assert!(monitor.monitor_event(event.clone()).is_err());
        let mut missing = event.clone();
        missing.input_labels.clear();
        assert!(monitor.monitor_event(missing).is_err());
        let mut missing = event;
        missing.output_labels.clear();
        assert!(monitor.monitor_event(missing).is_err());
        assert_eq!(monitor.get_stats().violation_count, 3);
    }

    #[test]
    fn test_ni_monitor_basic() {
        let config = NIMonitorConfig::default();
        let mut monitor = NIMonitor::new(config);

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Internal],
            output_labels: vec![SecurityLabel::Confidential],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        let result = monitor.monitor_event(event);
        assert!(result.is_ok());
        assert_eq!(monitor.get_stats().total_prefixes, 1);
    }

    #[test]
    fn test_ni_monitor_violation() {
        let mut config = NIMonitorConfig::default();
        config.strict_mode = true;
        let mut monitor = NIMonitor::new(config);

        let event = NIEvent {
            event_id: "event1".to_string(),
            timestamp: 1000,
            session_id: "session1".to_string(),
            user_id: "user1".to_string(),
            operation: "read".to_string(),
            input_labels: vec![SecurityLabel::Secret],
            output_labels: vec![SecurityLabel::Public],
            data_paths: vec!["$.data".to_string()],
            metadata: HashMap::new(),
        };

        let result = monitor.monitor_event(event);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Non-interference violation"));
    }

    #[test]
    fn test_prefix_integrity() {
        let config = NIMonitorConfig::default();
        let _monitor = NIMonitor::new(config);

        // Create a test prefix
        let prefix = NIPrefix::new(
            "test_prefix".to_string(),
            SecurityLabel::Internal,
            SecurityLabel::Public,
        );

        let hash = prefix.get_hash();
        assert_eq!(hash.len(), 64);
        assert!(hash.bytes().all(|b| b.is_ascii_hexdigit()));
        assert_eq!(prefix.get_hash(), hash);
    }

    #[test]
    fn test_prefix_digest_detects_changed_event_content() {
        let mut state = NIMonitorState::new(NIMonitorConfig::default());
        let event = NIEvent {
            event_id: "event".into(),
            timestamp: 1000,
            session_id: "session".into(),
            user_id: "user".into(),
            operation: "read".into(),
            input_labels: vec![SecurityLabel::Internal],
            output_labels: vec![SecurityLabel::Internal],
            data_paths: vec!["$.data".into()],
            metadata: HashMap::from([("a".into(), "1".into()), ("b".into(), "2".into())]),
        };
        state.add_event(event.clone()).unwrap();
        let id = state.generate_prefix_id(&event);
        assert!(state.verify_prefix_integrity(&id).unwrap());
        let original = state.prefixes[&id].clone();
        let mut reordered = original.clone();
        reordered.events[0].metadata = HashMap::from([("b".into(), "2".into()), ("a".into(), "1".into())]);
        assert_eq!(original.get_hash(), reordered.get_hash());

        let mut changed = original.clone();
        changed.events[0].output_labels = vec![SecurityLabel::Public];
        assert_ne!(original.get_hash(), changed.get_hash());
        let mut changed = original.clone();
        changed.events[0].data_paths = vec!["$.other".into()];
        assert_ne!(original.get_hash(), changed.get_hash());

        state.prefixes.get_mut(&id).unwrap().events[0].user_id = "other".into();
        assert!(!state.verify_prefix_integrity(&id).unwrap());
        assert!(state.add_event(event).is_err());
    }

    #[test]
    fn test_untrusted_proof_hashes_never_establish_verification() {
        let mut state = NIMonitorState::new(NIMonitorConfig::default());
        let mut hashes = ProofHashes::new();
        hashes.compute_from_files("policy", "automata", "labeler");
        state.update_proof_hashes(hashes);
        assert!(!state.generate_bridge_guarantee().proof_verification);
        state.config.proof_hash_verification = false;
        assert!(!state.generate_bridge_guarantee().proof_verification);
    }

    #[test]
    fn test_prefix_grouping_at_capacity() {
        let mut config = NIMonitorConfig::default();
        config.max_prefixes = 100;
        let mut monitor = NIMonitor::new(config);

        // Sequential events share 100 session/operation/label groups.
        for i in 0..1000 {
            let event = NIEvent {
                event_id: format!("event_{}", i),
                timestamp: 1000 + i as u64,
                session_id: format!("session_{}", i % 100),
                user_id: format!("user_{}", i % 50),
                operation: "read".to_string(),
                input_labels: vec![SecurityLabel::Internal],
                output_labels: vec![SecurityLabel::Internal],
                data_paths: vec![format!("$.data_{}", i)],
                metadata: HashMap::new(),
            };

            let result = monitor.monitor_event(event);
            assert!(result.is_ok());
        }

        let stats = monitor.get_stats();
        assert_eq!(stats.total_prefixes, 100);
        assert_eq!(monitor.get_prefixes().values().map(|p| p.events.len()).sum::<usize>(), 1000);
        assert_eq!(stats.active_sessions, 100);
    }

    #[test]
    fn test_proof_hashes() {
        let mut hashes = ProofHashes::new();

        // Test hash computation
        hashes.compute_from_files("policy content", "automata content", "labeler content");

        assert!(!hashes.policy_proof_hash.is_empty());
        assert!(!hashes.automata_hash.is_empty());
        assert!(!hashes.labeler_hash.is_empty());
        assert!(!hashes.ni_bridge_hash.is_empty());
    }

    #[test]
    fn test_bridge_guarantee() {
        let config = NIMonitorConfig::default();
        let monitor = NIMonitor::new(config);

        let guarantee = monitor.generate_bridge_guarantee();

        assert_eq!(guarantee.theorem_reference, "ni-bridge");
        assert_eq!(guarantee.global_ni_claim, "global_non_interference");
        assert!(!guarantee.bridge_conditions.is_empty());
    }

    #[test]
    fn test_ni_monitor_verdict_consistency() {
        let config = NIMonitorConfig::default();
        let mut monitor = NIMonitor::new(config);

        for i in 0..10_000 {
            let event = NIEvent {
                event_id: format!("prefix_{}", i),
                timestamp: 1000 + i as u64,
                session_id: format!("session_{}", i % 100),
                user_id: format!("user_{}", i % 50),
                operation: "read".to_string(),
                input_labels: vec![SecurityLabel::Internal],
                output_labels: vec![SecurityLabel::Internal],
                data_paths: vec![format!("$.path_{}", i)],
                metadata: HashMap::new(),
            };
            assert!(monitor.monitor_event(event).is_ok());
        }

        assert_eq!(monitor.get_stats().total_prefixes, 100);
        assert_eq!(monitor.get_prefixes().values().map(|p| p.events.len()).sum::<usize>(), 10_000);
        assert_eq!(monitor.get_stats().violation_count, 0);
    }
}
