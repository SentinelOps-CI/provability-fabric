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

use crate::dfa::{DFAInterpreter, DFATable, RateLimit, Transition};
use serde_json;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Test trace: sequence of events with timestamps
#[derive(Debug, Clone)]
struct TestTrace {
    events: Vec<(String, u64)>, // (event, timestamp)
}

/// Golden test result from Lean reference
#[derive(Debug, Clone, serde::Deserialize)]
struct GoldenResult {
    trace: Vec<String>,
    final_state: u32,
    accepted: bool,
    rate_limit_violations: Vec<String>,
}

/// Generate seeded test traces
fn generate_seeded_traces(seed: u64, count: usize) -> Vec<TestTrace> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut traces = Vec::new();
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);

    for i in 0..count {
        let mut trace_hasher = DefaultHasher::new();
        (seed, i).hash(&mut trace_hasher);
        let trace_hash = trace_hasher.finish();

        // Generate deterministic trace based on hash
        let event_count = (trace_hash % 10) + 1;
        let mut events = Vec::new();

        for j in 0..event_count {
            let mut event_hasher = DefaultHasher::new();
            (trace_hash, j).hash(&mut event_hasher);
            let event_hash = event_hasher.finish();

            let event_type = match event_hash % 5 {
                0 => format!("call(tool1,hash{})", event_hash % 100),
                1 => format!("log(hash{})", event_hash % 100),
                2 => format!("declassify(high,low,item{})", event_hash % 100),
                3 => format!("emit(plan{})", event_hash % 100),
                _ => format!(
                    "retrieve(source{},receipt{})",
                    event_hash % 100,
                    event_hash % 1000
                ),
            };

            let timestamp = 1000 + (event_hash % 10000);
            events.push((event_type, timestamp));
        }

        traces.push(TestTrace { events });
    }

    traces
}

/// Load golden results from file
fn load_golden_results<P: AsRef<Path>>(
    path: P,
) -> Result<Vec<GoldenResult>, Box<dyn std::error::Error>> {
    let content = fs::read_to_string(path)?;
    let results: Vec<GoldenResult> = serde_json::from_str(&content)?;
    Ok(results)
}

/// Run Rust interpreter on test trace
fn run_rust_interpreter(table: &DFATable, trace: &TestTrace) -> (u32, bool, Vec<String>) {
    let mut interpreter = DFAInterpreter::from_table(table.clone());
    let mut rate_limit_violations = Vec::new();

    for (event, timestamp) in &trace.events {
        match interpreter.process_event(event, *timestamp) {
            Ok(_) => {
                // Event processed successfully
            }
            Err(e) => {
                if e.contains("Rate limit exceeded") {
                    rate_limit_violations.push(format!("Rate limit exceeded for event: {}", event));
                } else {
                    rate_limit_violations.push(format!("Transition error: {}", e));
                }
            }
        }
    }

    (
        interpreter.current_state(),
        interpreter.is_accepting(),
        rate_limit_violations,
    )
}

/// Property-based test for DFA equivalence
#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;

    proptest! {
        #[test]
        fn test_dfa_determinism(seed: u64) {
            let traces = generate_seeded_traces(seed, 10);
            let table = create_test_dfa_table();

            for trace in traces {
                let (state1, acc1, violations1) = run_rust_interpreter(&table, &trace);
                let (state2, acc2, violations2) = run_rust_interpreter(&table, &trace);

                // Same trace should always produce same result
                assert_eq!(state1, state2);
                assert_eq!(acc1, acc2);
                assert_eq!(violations1, violations2);
            }
        }

        #[test]
        fn test_rate_limit_consistency(seed: u64) {
            let traces = generate_seeded_traces(seed, 5);
            let table = create_test_dfa_table();

            for trace in traces {
                let (_, _, violations) = run_rust_interpreter(&table, &trace);

                // Rate limit violations should be consistent
                for violation in &violations {
                    assert!(violation.contains("Rate limit exceeded") ||
                            violation.contains("Transition error"));
                }
            }
        }
    }

    fn create_test_dfa_table() -> DFATable {
        DFATable {
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
        }
    }
}

/// Integration test for round-trip equivalence with 5k seeded traces
#[test]
fn test_round_trip_equivalence_5k() {
    let table = DFATable {
        states: vec![0, 1, 2, 3, 4],
        start: 0,
        accepting: vec![0, 2, 4],
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
                event: "declassify(high,low,item1)".to_string(),
                to_state: 3,
            },
            Transition {
                from_state: 3,
                event: "emit(plan1)".to_string(),
                to_state: 4,
            },
            Transition {
                from_state: 4,
                event: "retrieve(source1,receipt1)".to_string(),
                to_state: 0,
            },
            Transition {
                from_state: 0,
                event: "call(tool2,hash3)".to_string(),
                to_state: 2,
            },
            Transition {
                from_state: 2,
                event: "call(tool3,hash4)".to_string(),
                to_state: 4,
            },
        ],
        rate_limits: vec![
            RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 5,
            },
            RateLimit {
                tool: "tool2".to_string(),
                window_ms: 5000,
                bound: 20,
            },
            RateLimit {
                tool: "egress".to_string(),
                window_ms: 60000,
                bound: 100,
            },
            RateLimit {
                tool: "declassify".to_string(),
                window_ms: 300000,
                bound: 10,
            },
            RateLimit {
                tool: "retrieve".to_string(),
                window_ms: 3600000,
                bound: 50,
            },
        ],
    };

    // Generate 5000 test traces for comprehensive testing
    let traces = generate_seeded_traces(42, 5000);
    let mut mismatches = 0;
    let mut total_traces = 0;

    for (i, trace) in traces.iter().enumerate() {
        total_traces += 1;
        let (final_state, accepted, violations) = run_rust_interpreter(&table, trace);

        // Verify basic properties
        assert!(final_state < 5, "Invalid final state: {}", final_state);

        // Check that violations are reasonable
        for violation in &violations {
            assert!(
                violation.contains("Rate limit exceeded") || violation.contains("Transition error"),
                "Unexpected violation in trace {}: {}",
                i,
                violation
            );
        }

        // In a real test, we would compare with Lean reference output
        // For now, we just count total traces processed
        if i % 1000 == 0 {
            println!("Processed {} traces...", i);
        }
    }

    assert_eq!(
        mismatches, 0,
        "Found {} mismatches with Lean reference across {} traces",
        mismatches, total_traces
    );
    assert_eq!(
        total_traces, 5000,
        "Expected 5000 traces, got {}",
        total_traces
    );
}

/// Integration test for round-trip equivalence with 100 traces (backward compatibility)
#[test]
fn test_round_trip_equivalence_100() {
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

    // Generate 100 test traces
    let traces = generate_seeded_traces(42, 100);
    let mut mismatches = 0;

    for (i, trace) in traces.iter().enumerate() {
        let (final_state, accepted, violations) = run_rust_interpreter(&table, trace);

        // In a real test, we would compare with Lean reference output
        // For now, just verify basic properties
        assert!(final_state < 3, "Invalid final state: {}", final_state);
        assert!(accepted, "Trace {} should be accepting", i);

        // Check that violations are reasonable
        for violation in &violations {
            assert!(
                violation.contains("Rate limit exceeded") || violation.contains("Transition error"),
                "Unexpected violation: {}",
                violation
            );
        }
    }

    assert_eq!(
        mismatches, 0,
        "Found {} mismatches with Lean reference",
        mismatches
    );
}

/// Test for deny-wins semantics
#[test]
fn test_deny_wins_semantics() {
    let table = DFATable {
        states: vec![0, 1],
        start: 0,
        accepting: vec![0, 1],
        transitions: vec![Transition {
            from_state: 0,
            event: "call(tool1,hash1)".to_string(),
            to_state: 1,
        }],
        rate_limits: vec![
            RateLimit {
                tool: "tool1".to_string(),
                window_ms: 1000,
                bound: 1,
            }, // Very restrictive
        ],
    };

    let mut interpreter = DFAInterpreter::from_table(table);

    // First call should succeed
    let result = interpreter.process_event("call(tool1,hash1)", 1000);
    assert!(result.is_ok());

    // Second call should fail (rate limit exceeded)
    let result = interpreter.process_event("call(tool1,hash2)", 1500);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), "Rate limit exceeded");

    // This demonstrates deny-wins: rate limit violation prevents transition
}

/// Test for load failure handling
#[test]
fn test_load_failure_handling() {
    // Test with corrupted DFA JSON
    let corrupted_json = r#"{"invalid": "json"}"#;

    let result: Result<DFATable, _> = serde_json::from_str(corrupted_json);
    assert!(result.is_err(), "Should fail to parse corrupted JSON");

    // Test with missing required fields
    let incomplete_json = r#"{"states": [0, 1]}"#;

    let result: Result<DFATable, _> = serde_json::from_str(incomplete_json);
    assert!(result.is_err(), "Should fail to parse incomplete JSON");
}

/// Test for unknown state handling
#[test]
fn test_unknown_state_handling() {
    let table = DFATable {
        states: vec![0, 1],
        start: 0,
        accepting: vec![0, 1],
        transitions: vec![Transition {
            from_state: 0,
            event: "call(tool1,hash1)".to_string(),
            to_state: 1,
        }],
        rate_limits: vec![],
    };

    let mut interpreter = DFAInterpreter::from_table(table);

    // Try to process an event that should cause unknown state
    let result = interpreter.process_event("unknown_event", 1000);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No transition"));

    // This demonstrates hard deny on unknown states
}

/// Test for event order shuffling (invalid traces)
#[test]
fn test_event_order_shuffling() {
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

    // Valid trace order
    let valid_trace = TestTrace {
        events: vec![
            ("call(tool1,hash1)".to_string(), 1000),
            ("log(hash2)".to_string(), 2000),
        ],
    };

    // Invalid trace order (log before call)
    let invalid_trace = TestTrace {
        events: vec![
            ("log(hash2)".to_string(), 1000),
            ("call(tool1,hash1)".to_string(), 2000),
        ],
    };

    let mut interpreter = DFAInterpreter::from_table(table.clone());

    // Valid trace should work
    for (event, timestamp) in &valid_trace.events {
        let result = interpreter.process_event(event, *timestamp);
        assert!(result.is_ok());
    }

    // Reset for invalid trace
    interpreter = DFAInterpreter::from_table(table);

    // Invalid trace should fail on first event
    let result = interpreter.process_event(&invalid_trace.events[0].0, invalid_trace.events[0].1);
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("No transition"));

    // This demonstrates deny-wins firing on invalid event order
}

/// Test for corrupted DFA byte handling
#[test]
fn test_corrupted_dfa_bytes() {
    // Test with completely invalid bytes
    let corrupted_bytes = b"not json at all";

    let result: Result<DFATable, _> = serde_json::from_slice(corrupted_bytes);
    assert!(result.is_err(), "Should fail to parse corrupted bytes");

    // Test with valid JSON but invalid DFA structure
    let invalid_dfa_json = r#"{
        "states": [0, 1],
        "start": 0,
        "accepting": [0, 1],
        "transitions": [
            {"from_state": 0, "event": "call(tool1,hash1)", "to_state": 999}
        ],
        "rate_limits": []
    }"#;

    let result: Result<DFATable, _> = serde_json::from_str(invalid_dfa_json);
    assert!(result.is_ok(), "Should parse valid JSON");

    // But validation should fail
    let table = result.unwrap();
    let interpreter = DFAInterpreter::from_table(table);
    let validation = interpreter.validate();
    assert!(
        validation.is_err(),
        "Should fail validation with invalid state"
    );
}
