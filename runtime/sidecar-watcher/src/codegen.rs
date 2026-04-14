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

use crate::dfa::{CallTag, EmitBucket, EventKind, StateId};
use std::collections::HashMap;
use std::fmt;

/// Code generation for hot rules with compile-time optimization
pub struct HotRuleCodegen {
    /// Hot rules identified for code generation
    hot_rules: Vec<HotRule>,
    /// Generated code templates
    code_templates: HashMap<String, String>,
}

/// Hot rule definition for code generation
#[derive(Debug, Clone)]
pub struct HotRule {
    pub rule_id: String,
    pub event_patterns: Vec<EventPattern>,
    pub state_transitions: Vec<StateTransition>,
    pub frequency: u64, // How often this rule is triggered
    pub priority: u8,   // 0 = highest priority
}

/// Event pattern for hot rule matching
#[derive(Debug, Clone)]
pub struct EventPattern {
    pub event_kind: EventKind,
    pub call_tag: Option<CallTag>,
    pub emit_bucket: Option<EmitBucket>,
    pub tool_name: Option<String>,
}

/// State transition in hot rule
#[derive(Debug, Clone)]
pub struct StateTransition {
    pub from_state: StateId,
    pub to_state: StateId,
    pub condition: EventPattern,
}

/// Generated monitor code
#[derive(Debug, Clone)]
pub struct GeneratedMonitor {
    pub monitor_name: String,
    pub rust_code: String,
    pub performance_metrics: PerformanceMetrics,
}

/// Performance metrics for generated code
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub estimated_cycles: u64,
    pub cache_misses: u64,
    pub branch_predictions: u64,
    pub memory_accesses: u64,
}

impl Default for HotRuleCodegen {
    fn default() -> Self {
        Self::new()
    }
}

impl HotRuleCodegen {
    /// Create new hot rule code generator
    pub fn new() -> Self {
        Self {
            hot_rules: Vec::new(),
            code_templates: Self::initialize_templates(),
        }
    }

    /// Add a hot rule for code generation
    pub fn add_hot_rule(&mut self, rule: HotRule) {
        self.hot_rules.push(rule);
        // Sort by frequency and priority
        self.hot_rules.sort_by(|a, b| {
            b.frequency
                .cmp(&a.frequency)
                .then_with(|| a.priority.cmp(&b.priority))
        });
    }

    /// Generate optimized monitor code for hot rules
    pub fn generate_monitors(&self) -> Vec<GeneratedMonitor> {
        let mut monitors = Vec::new();

        for rule in &self.hot_rules {
            let monitor = self.generate_monitor_for_rule(rule);
            monitors.push(monitor);
        }

        monitors
    }

    /// Generate monitor code for a specific hot rule
    fn generate_monitor_for_rule(&self, rule: &HotRule) -> GeneratedMonitor {
        let monitor_name = format!("{}Monitor", rule.rule_id);

        // Generate the Rust code for this monitor
        let rust_code = self.generate_rust_code(rule);

        // Calculate performance metrics
        let performance_metrics = self.calculate_performance_metrics(rule);

        GeneratedMonitor {
            monitor_name,
            rust_code,
            performance_metrics,
        }
    }

    /// Generate Rust code for a hot rule
    fn generate_rust_code(&self, rule: &HotRule) -> String {
        let mut code = String::new();

        // Generate struct definition
        code.push_str(&format!(
            "#[derive(Debug, Clone)]\n\
            pub struct {}Monitor {{\n\
                current_state: StateId,\n\
                state_count: u64,\n\
                transition_count: u64,\n\
            }}\n\n",
            rule.rule_id
        ));

        // Generate impl block
        code.push_str(&format!(
            "impl {}Monitor {{\n\
                pub fn new() -> Self {{\n\
                    Self {{\n\
                        current_state: 0,\n\
                        state_count: 0,\n\
                        transition_count: 0,\n\
                    }}\n\
                }}\n\n",
            rule.rule_id
        ));

        // Generate hot path step function
        code.push_str(
            "    #[inline(always)]\n\
            pub fn step(&mut self, event: &Event) -> StateId {\n\
                self.state_count += 1;\n\
                \n\
                let next_state = match event.kind {\n",
        );

        // Generate match arms for each event pattern
        for pattern in &rule.event_patterns {
            code.push_str(&self.generate_match_arm(pattern, rule));
        }

        // Add default case
        code.push_str(
            "                    _ => self.current_state,\n\
                }};\n\
                \n\
                if next_state != self.current_state {{\n\
                    self.transition_count += 1;\n\
                    self.current_state = next_state;\n\
                }}\n\
                \n\
                next_state\n\
            }}\n\n",
        );

        // Generate utility methods
        code.push_str(
            "    pub fn current_state(&self) -> StateId {\n\
                self.current_state\n\
            }\n\n\
            pub fn get_metrics(&self) -> (u64, u64) {\n\
                (self.state_count, self.transition_count)\n\
            }\n\n\
            pub fn reset(&mut self) {\n\
                self.current_state = 0;\n\
                self.state_count = 0;\n\
                self.transition_count = 0;\n\
            }\n\
        }\n",
        );

        code
    }

    /// Generate match arm for an event pattern
    fn generate_match_arm(&self, pattern: &EventPattern, rule: &HotRule) -> String {
        let mut arm = String::new();

        arm.push_str(&format!(
            "                    EventKind::{:?} => {{\n",
            pattern.event_kind
        ));

        // Add conditions for call_tag and emit_bucket
        match pattern.event_kind {
            EventKind::Call => {
                if let Some(tag) = pattern.call_tag {
                    arm.push_str(&format!(
                        "                        if event.call_tag == {} {{\n",
                        tag
                    ));
                }
            }
            EventKind::Emit => {
                if let Some(bucket) = pattern.emit_bucket {
                    arm.push_str(&format!(
                        "                        if event.emit_bucket == {} {{\n",
                        bucket
                    ));
                }
            }
            _ => {}
        }

        // Add tool name condition if specified
        if let Some(ref tool_name) = pattern.tool_name {
            arm.push_str(&format!(
                "                        if event.tool_name == \"{}\" {{\n",
                tool_name
            ));
        }

        // Find the transition for this pattern
        if let Some(transition) = rule
            .state_transitions
            .iter()
            .find(|t| t.condition.event_kind == pattern.event_kind)
        {
            arm.push_str(&format!(
                "                            {}\n",
                transition.to_state
            ));
        } else {
            arm.push_str("                            self.current_state\n");
        }

        // Close all the if statements
        if pattern.tool_name.is_some() {
            arm.push_str("                        } else {\n                            self.current_state\n                        }\n");
        }
        if matches!(pattern.event_kind, EventKind::Call | EventKind::Emit) {
            arm.push_str("                        } else {\n                            self.current_state\n                        }\n");
        }

        arm.push_str("                    }\n");
        arm
    }

    /// Calculate performance metrics for generated code
    fn calculate_performance_metrics(&self, rule: &HotRule) -> PerformanceMetrics {
        let mut estimated_cycles = 1; // Base cycle for function call
        let cache_misses = 0;
        let mut branch_predictions = 0;
        let mut memory_accesses = 1; // Access to self.current_state

        // Estimate based on event patterns
        for pattern in &rule.event_patterns {
            estimated_cycles += 2; // Match on event.kind
            branch_predictions += 1;

            match pattern.event_kind {
                EventKind::Call => {
                    if pattern.call_tag.is_some() {
                        estimated_cycles += 1; // Compare call_tag
                        branch_predictions += 1;
                    }
                }
                EventKind::Emit => {
                    if pattern.emit_bucket.is_some() {
                        estimated_cycles += 1; // Compare emit_bucket
                        branch_predictions += 1;
                    }
                }
                _ => {}
            }

            if pattern.tool_name.is_some() {
                estimated_cycles += 3; // String comparison
                memory_accesses += 1; // Access to event.tool_name
            }
        }

        // Add transition logic
        estimated_cycles += 2; // Compare and assign
        memory_accesses += 1; // Write to self.current_state

        PerformanceMetrics {
            estimated_cycles,
            cache_misses,
            branch_predictions,
            memory_accesses,
        }
    }

    /// Initialize code generation templates
    fn initialize_templates() -> HashMap<String, String> {
        let mut templates = HashMap::new();

        templates.insert(
            "monitor_struct".to_string(),
            "#[derive(Debug, Clone)]\npub struct {}Monitor {{\n    current_state: StateId,\n    state_count: u64,\n    transition_count: u64,\n}".to_string(),
        );

        templates.insert(
            "hot_path_step".to_string(),
            "#[inline(always)]\npub fn step(&mut self, event: &Event) -> StateId {{\n    self.state_count += 1;\n    \n    let next_state = match event.kind {{\n        // Generated match arms\n    }};\n    \n    if next_state != self.current_state {{\n        self.transition_count += 1;\n        self.current_state = next_state;\n    }}\n    \n    next_state\n}}".to_string(),
        );

        templates
    }

    /// Generate optimized DFA step function
    pub fn generate_optimized_dfa_step(&self) -> String {
        let mut code = String::new();

        code.push_str(
            "/// Optimized DFA step function with compile-time dispatch\n\
            #[inline(always)]\n\
            pub fn optimized_step(mut state: StateId, event: &Event) -> StateId {\n\
                match event.kind {\n",
        );

        // Generate optimized match arms for each event kind
        for event_kind in [
            EventKind::Call,
            EventKind::Emit,
            EventKind::Log,
            EventKind::Declassify,
            EventKind::Retrieve,
            EventKind::DataQuery,
            EventKind::Search,
            EventKind::Fetch,
            EventKind::Get,
            EventKind::Compute,
            EventKind::Analyze,
            EventKind::Transform,
            EventKind::Aggregate,
            EventKind::Notify,
            EventKind::Alert,
            EventKind::Report,
            EventKind::Export,
            EventKind::Validate,
            EventKind::Verify,
            EventKind::Audit,
            EventKind::ComplianceCheck,
        ] {
            code.push_str(&format!(
                "                    EventKind::{:?} => {{\n\
                        // Optimized dispatch for {:?} events\n\
                        match event.kind {{\n\
                            EventKind::Call => DFA_CALL[state as usize][event.call_tag as usize],\n\
                            EventKind::Emit => DFA_EMIT[state as usize][event.emit_bucket as usize],\n\
                            _ => state, // Self-loop for unsupported events\n\
                        }}\n\
                    }}\n",
                event_kind, event_kind
            ));
        }

        code.push_str(
            "                }\n\
            }\n",
        );

        code
    }

    /// Generate performance benchmark code
    pub fn generate_benchmark_code(&self, monitor_name: &str) -> String {
        format!(
            "#[cfg(test)]\n\
            mod {}_benchmarks {{\n\
                use super::*;\n\
                use std::time::Instant;\n\
                \n\
                #[test]\n\
                fn benchmark_{}_hot_path() {{\n\
                    let mut monitor = {}Monitor::new();\n\
                    let events = create_test_events(100000);\n\
                    \n\
                    let start = Instant::now();\n\
                    for event in &events {{\n\
                        monitor.step(event);\n\
                    }}\n\
                    let duration = start.elapsed();\n\
                    \n\
                    assert!(duration.as_millis() < 1, \"Hot path too slow: {{:?}}\", duration);\n\
                    println!(\"100k {} operations took: {{:?}}\", duration);\n\
                }}\n\
                \n\
                fn create_test_events(count: usize) -> Vec<Event> {{\n\
                    (0..count)\n\
                        .map(|i| Event::new(\n\
                            EventKind::Call,\n\
                            (i % 256) as u16,\n\
                            (i % 256) as u16,\n\
                            format!(\"tool{{}}\", i % 10)\n\
                        ))\n\
                        .collect()\n\
                }}\n\
            }}",
            monitor_name.to_lowercase(),
            monitor_name.to_lowercase(),
            monitor_name,
            monitor_name.to_lowercase()
        )
    }

    /// Get code generation statistics
    pub fn get_stats(&self) -> HashMap<String, usize> {
        let mut stats = HashMap::new();
        stats.insert("hot_rules_count".to_string(), self.hot_rules.len());
        stats.insert("templates_count".to_string(), self.code_templates.len());

        let total_patterns: usize = self
            .hot_rules
            .iter()
            .map(|rule| rule.event_patterns.len())
            .sum();
        stats.insert("total_patterns".to_string(), total_patterns);

        stats
    }
}

impl fmt::Display for GeneratedMonitor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Monitor: {}\n\n{}", self.monitor_name, self.rust_code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hot_rule_codegen() {
        let mut codegen = HotRuleCodegen::new();

        let hot_rule = HotRule {
            rule_id: "CallMonitor".to_string(),
            event_patterns: vec![EventPattern {
                event_kind: EventKind::Call,
                call_tag: Some(1),
                emit_bucket: None,
                tool_name: Some("tool1".to_string()),
            }],
            state_transitions: vec![StateTransition {
                from_state: 0,
                to_state: 1,
                condition: EventPattern {
                    event_kind: EventKind::Call,
                    call_tag: Some(1),
                    emit_bucket: None,
                    tool_name: Some("tool1".to_string()),
                },
            }],
            frequency: 1000,
            priority: 0,
        };

        codegen.add_hot_rule(hot_rule);
        let monitors = codegen.generate_monitors();

        assert_eq!(monitors.len(), 1);
        assert!(monitors[0].rust_code.contains("CallMonitor"));
    }

    #[test]
    fn test_performance_metrics() {
        let codegen = HotRuleCodegen::new();

        let hot_rule = HotRule {
            rule_id: "TestMonitor".to_string(),
            event_patterns: vec![EventPattern {
                event_kind: EventKind::Call,
                call_tag: Some(1),
                emit_bucket: None,
                tool_name: Some("tool1".to_string()),
            }],
            state_transitions: vec![],
            frequency: 100,
            priority: 1,
        };

        let metrics = codegen.calculate_performance_metrics(&hot_rule);
        assert!(metrics.estimated_cycles > 0);
        assert!(metrics.branch_predictions > 0);
    }

    #[test]
    fn test_optimized_dfa_step_generation() {
        let codegen = HotRuleCodegen::new();
        let code = codegen.generate_optimized_dfa_step();

        assert!(code.contains("optimized_step"));
        assert!(code.contains("match event.kind"));
        assert!(code.contains("DFA_CALL"));
        assert!(code.contains("DFA_EMIT"));
    }
}
