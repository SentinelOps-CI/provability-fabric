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

use serde_json;
use sidecar_watcher::dfa::{DFAInterpreter, DFATable, OptimizedDFA, RateLimit, Transition};
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

/// Table-scanning reference for exact transitions and closed rate windows.
/// This is a Rust reference comparison, not Lean equivalence evidence.
fn compare_against_reference(table: &DFATable, events: &[(String, u64)]) -> (usize, usize) {
    let mut legacy = DFAInterpreter::from_table(table.clone());
    let mut indexed = OptimizedDFA::from_table(table.clone()).unwrap();
    let mut state = table.start;
    let mut histories: Vec<Vec<u64>> = vec![Vec::new(); table.rate_limits.len()];
    let mut accepted = 0;
    let mut denied = 0;
    for (event, time) in events {
        let next = table.transitions.iter()
            .find(|edge| edge.from_state == state && edge.event == *event)
            .map(|edge| edge.to_state);
        assert_eq!(indexed.step(state, event), next);
        let limited = table.rate_limits.iter().enumerate().any(|(i, limit)| {
            event.contains(&limit.tool) && histories[i].iter()
                .filter(|t| **t >= time.saturating_sub(limit.window_ms as u64))
                .count() >= limit.bound as usize
        });
        let expected = if limited {
            Err("Rate limit exceeded".to_string())
        } else if let Some(next) = next {
            state = next;
            for (i, limit) in table.rate_limits.iter().enumerate() {
                if event.contains(&limit.tool) {
                    histories[i].push(*time);
                    histories[i].retain(|t| *t >= time.saturating_sub(limit.window_ms as u64));
                }
            }
            Ok(true)
        } else {
            Err(format!("No transition for state {} with event {}", state, event))
        };
        assert_eq!(legacy.process_event(event, *time), expected);
        assert_eq!(indexed.process_event(event, *time), expected);
        assert_eq!(legacy.current_state(), state);
        assert_eq!(indexed.current_state(), state);
        assert_eq!(legacy.is_accepting(), table.accepting.contains(&state));
        assert_eq!(indexed.is_accepting(state), table.accepting.contains(&state));
        if expected.is_ok() { accepted += 1; } else { denied += 1; }
    }
    (accepted, denied)
}

fn reference_table() -> DFATable {
    DFATable {
        states: vec![900, 42, 7, 256],
        start: 42,
        accepting: vec![42, 900],
        transitions: vec![
            Transition { from_state: 42, event: "call(tool1,hash1)".into(), to_state: 7 },
            Transition { from_state: 7, event: "call(tool2,hash1)".into(), to_state: 256 },
            Transition { from_state: 7, event: "call(tool1,hash1)".into(), to_state: 7 },
            Transition { from_state: 256, event: "log(hash1)".into(), to_state: 900 },
            Transition { from_state: 256, event: "log(hash2)".into(), to_state: 42 },
            Transition { from_state: 900, event: "emit(plan1)".into(), to_state: 42 },
        ],
        rate_limits: vec![RateLimit { tool: "tool1".into(), window_ms: 1000, bound: 2 }],
    }
}

#[test]
fn test_indexed_reference_equivalence_5k() {
    let table = reference_table();
    let alphabet = [
        "call(tool1,hash1)", "call(tool2,hash1)", "call(tool1,hash2)",
        "log(hash1)", "log(hash2)", "emit(plan1)", "emit(plan2)", "unknown",
    ];
    let mut seed = 42u64;
    let mut totals = (0, 0);
    for _ in 0..5000 {
        let mut trace = Vec::new();
        for i in 0..24 {
            seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
            let event = alphabet[(seed >> 32) as usize % alphabet.len()];
            trace.push((event.to_string(), 1000 + i * 150));
        }
        let (accepted, denied) = compare_against_reference(&table, &trace);
        totals.0 += accepted;
        totals.1 += denied;
    }
    assert_eq!(totals.0 + totals.1, 120_000);
    assert!(totals.0 > 0 && totals.1 > 0);
}

#[test]
fn test_indexed_reference_rate_limit_boundary_and_distinct_symbols() {
    let table = reference_table();
    let trace = [
        ("call(tool1,hash1)", 1000), ("call(tool1,hash1)", 1500),
        ("call(tool1,hash1)", 2000), ("call(tool1,hash1)", 2001),
        ("call(tool2,hash1)", 2002), ("log(hash2)", 2003),
        ("log(hash1)", 2004), ("call(tool1,hash2)", 4000),
        ("call(tool1,hash1)", 4001), ("call(tool2,hash1)", 4002),
        ("log(hash1)", 4003), ("emit(plan1)", 4004),
    ].into_iter().map(|(event, time)| (event.to_string(), time)).collect::<Vec<_>>();
    assert_eq!(compare_against_reference(&table, &trace), (9, 3));
    let mut invalid = table.clone();
    invalid.transitions.push(invalid.transitions[0].clone());
    assert!(OptimizedDFA::from_table(invalid).is_err());
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
