#!/usr/bin/env python3
"""
Generate comprehensive DFA test traces for equivalence testing.
Creates 5k seeded traces with various edge cases and rate limit scenarios.
"""

import json
import random
import argparse
from pathlib import Path
from typing import List, Dict, Any, Tuple
import time


class DFATraceGenerator:
    """Generate deterministic DFA test traces for equivalence testing."""

    def __init__(self, seed: int = 42):
        self.seed = seed
        random.seed(seed)

    def generate_event(
        self, event_hash: int, timestamp: int
    ) -> Tuple[str, Dict[str, Any]]:
        """Generate a deterministic event based on hash."""
        event_types = [
            "call(tool1,hash{})",
            "call(tool2,hash{})",
            "log(hash{})",
            "declassify(high,low,item{})",
            "emit(plan{})",
            "retrieve(source{},receipt{})",
        ]

        event_type_idx = event_hash % len(event_types)
        event_template = event_types[event_type_idx]

        if event_template.count("{}") == 1:
            event = event_template.format(event_hash % 1000)
        else:
            event = event_template.format(event_hash % 100, event_hash % 1000)

        return event, {
            "timestamp": timestamp,
            "event": event,
            "args_hash": f"hash_{event_hash:08x}",
        }

    def generate_trace(self, trace_id: int, max_events: int = 20) -> Dict[str, Any]:
        """Generate a single test trace."""
        # Use trace_id as seed for deterministic generation
        trace_seed = self.seed + trace_id
        random.seed(trace_seed)

        # Generate random number of events
        num_events = random.randint(1, max_events)
        events = []

        base_timestamp = 1000 + (trace_id * 100)

        for i in range(num_events):
            event_hash = hash(f"{trace_seed}_{i}") % (2**32)
            timestamp = base_timestamp + (i * random.randint(50, 200))

            event, event_data = self.generate_event(event_hash, timestamp)
            events.append(event_data)

        return {
            "trace_id": f"trace_{trace_id}",
            "seed": trace_seed,
            "events": events,
            "metadata": {
                "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "event_count": len(events),
                "time_span_ms": (
                    events[-1]["timestamp"] - events[0]["timestamp"] if events else 0
                ),
            },
        }

    def generate_rate_limit_test_traces(self) -> List[Dict[str, Any]]:
        """Generate traces specifically designed to test rate limiting."""
        rate_limit_traces = []

        # Test case: Rapid successive calls to trigger rate limit
        rapid_calls = {
            "trace_id": "rate_limit_rapid_calls",
            "seed": 9999,
            "events": [
                {
                    "timestamp": 1000,
                    "event": "call(tool1,hash1)",
                    "args_hash": "hash_001",
                },
                {
                    "timestamp": 1100,
                    "event": "call(tool1,hash2)",
                    "args_hash": "hash_002",
                },
                {
                    "timestamp": 1200,
                    "event": "call(tool1,hash3)",
                    "args_hash": "hash_003",
                },
                {
                    "timestamp": 1300,
                    "event": "call(tool1,hash4)",
                    "args_hash": "hash_004",
                },
                {
                    "timestamp": 1400,
                    "event": "call(tool1,hash5)",
                    "args_hash": "hash_005",
                },
                {
                    "timestamp": 1500,
                    "event": "call(tool1,hash6)",
                    "args_hash": "hash_006",
                },  # Should trigger rate limit
            ],
            "expected_rate_limit_violations": ["call(tool1,hash6)"],
            "metadata": {"test_type": "rate_limit_rapid_calls"},
        }
        rate_limit_traces.append(rapid_calls)

        # Test case: Clock wraparound
        wraparound_trace = {
            "trace_id": "rate_limit_wraparound",
            "seed": 9998,
            "events": [
                {"timestamp": 0, "event": "call(tool1,hash1)", "args_hash": "hash_001"},
                {"timestamp": 1, "event": "call(tool1,hash2)", "args_hash": "hash_002"},
            ],
            "expected_rate_limit_violations": [],
            "metadata": {"test_type": "rate_limit_wraparound"},
        }
        rate_limit_traces.append(wraparound_trace)

        return rate_limit_traces

    def generate_edge_case_traces(self) -> List[Dict[str, Any]]:
        """Generate traces for edge cases and error conditions."""
        edge_cases = []

        # Empty trace
        empty_trace = {
            "trace_id": "edge_case_empty",
            "seed": 9997,
            "events": [],
            "expected_final_state": 0,
            "expected_accept": True,
            "metadata": {"test_type": "edge_case_empty"},
        }
        edge_cases.append(empty_trace)

        # Invalid event
        invalid_event = {
            "trace_id": "edge_case_invalid_event",
            "seed": 9996,
            "events": [
                {
                    "timestamp": 1000,
                    "event": "invalid_event",
                    "args_hash": "hash_invalid",
                }
            ],
            "expected_error": "No transition for state 0 with event invalid_event",
            "metadata": {"test_type": "edge_case_invalid_event"},
        }
        edge_cases.append(invalid_event)

        # Event order shuffling (invalid)
        invalid_order = {
            "trace_id": "edge_case_invalid_order",
            "seed": 9995,
            "events": [
                {
                    "timestamp": 2000,
                    "event": "log(hash2)",
                    "args_hash": "hash_002",
                },  # log before call
                {
                    "timestamp": 1000,
                    "event": "call(tool1,hash1)",
                    "args_hash": "hash_001",
                },
            ],
            "expected_error": "No transition for state 0 with event log(hash2)",
            "metadata": {"test_type": "edge_case_invalid_order"},
        }
        edge_cases.append(invalid_order)

        return edge_cases

    def generate_comprehensive_suite(self, num_traces: int = 5000) -> Dict[str, Any]:
        """Generate comprehensive test suite with specified number of traces."""
        print(f"Generating {num_traces} test traces...")

        # Generate regular traces
        traces = []
        for i in range(num_traces):
            if i % 1000 == 0:
                print(f"Generated {i} traces...")
            traces.append(self.generate_trace(i))

        # Add rate limit test traces
        rate_limit_traces = self.generate_rate_limit_test_traces()
        traces.extend(rate_limit_traces)

        # Add edge case traces
        edge_case_traces = self.generate_edge_case_traces()
        traces.extend(edge_case_traces)

        # Create comprehensive test suite
        test_suite = {
            "test_suite_id": "comprehensive_equivalence_test_suite",
            "description": f"Comprehensive DFA test suite with {len(traces)} traces for bit-for-bit equivalence testing",
            "version": "v1",
            "bundle_id": "test-agent",
            "metadata": {
                "created_at": time.strftime("%Y-%m-%dT%H:%M:%SZ"),
                "total_traces": len(traces),
                "seed_range": [self.seed, self.seed + num_traces - 1],
                "event_types": ["call", "log", "declassify", "emit", "retrieve"],
                "rate_limit_windows": [1000, 5000, 60000, 300000, 3600000],
                "generator_seed": self.seed,
            },
            "dfa_table": {
                "states": [0, 1, 2, 3, 4],
                "start": 0,
                "accepting": [0, 2, 4],
                "transitions": [
                    {"from_state": 0, "event": "call(tool1,hash1)", "to_state": 1},
                    {"from_state": 1, "event": "log(hash2)", "to_state": 2},
                    {
                        "from_state": 2,
                        "event": "declassify(high,low,item1)",
                        "to_state": 3,
                    },
                    {"from_state": 3, "event": "emit(plan1)", "to_state": 4},
                    {
                        "from_state": 4,
                        "event": "retrieve(source1,receipt1)",
                        "to_state": 0,
                    },
                    {"from_state": 0, "event": "call(tool2,hash3)", "to_state": 2},
                    {"from_state": 2, "event": "call(tool3,hash4)", "to_state": 4},
                ],
                "rate_limits": [
                    {"tool": "tool1", "window_ms": 1000, "bound": 5},
                    {"tool": "tool2", "window_ms": 5000, "bound": 20},
                    {"tool": "egress", "window_ms": 60000, "bound": 100},
                    {"tool": "declassify", "window_ms": 300000, "bound": 10},
                    {"tool": "retrieve", "window_ms": 3600000, "bound": 50},
                ],
            },
            "test_traces": traces,
            "validation": {
                "total_events": sum(len(trace["events"]) for trace in traces),
                "unique_events": len(
                    set(event["event"] for trace in traces for event in trace["events"])
                ),
                "time_range_ms": {
                    "min": (
                        min(
                            min(event["timestamp"] for event in trace["events"])
                            for trace in traces
                            if trace["events"]
                        )
                        if traces
                        else 0
                    ),
                    "max": (
                        max(
                            max(event["timestamp"] for event in trace["events"])
                            for trace in traces
                            if trace["events"]
                        )
                        if traces
                        else 0
                    ),
                },
            },
        }

        return test_suite


def main():
    parser = argparse.ArgumentParser(description="Generate DFA test traces")
    parser.add_argument(
        "--output",
        "-o",
        default="artifact/golden/dfa_cases/",
        help="Output directory for test traces",
    )
    parser.add_argument(
        "--num-traces",
        "-n",
        type=int,
        default=5000,
        help="Number of traces to generate",
    )
    parser.add_argument(
        "--seed",
        "-s",
        type=int,
        default=42,
        help="Random seed for deterministic generation",
    )

    args = parser.parse_args()

    # Create output directory
    output_dir = Path(args.output)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate test suite
    generator = DFATraceGenerator(seed=args.seed)
    test_suite = generator.generate_comprehensive_suite(args.num_traces)

    # Save comprehensive test suite
    output_file = output_dir / "comprehensive_equivalence_test_suite.json"
    with open(output_file, "w") as f:
        json.dump(test_suite, f, indent=2)

    print(
        f"Generated comprehensive test suite with {len(test_suite['test_traces'])} traces"
    )
    print(f"Saved to: {output_file}")

    # Generate individual trace files for easier debugging
    traces_dir = output_dir / "individual_traces"
    traces_dir.mkdir(exist_ok=True)

    for i, trace in enumerate(
        test_suite["test_traces"][:100]
    ):  # Save first 100 for debugging
        trace_file = traces_dir / f"trace_{i:04d}.json"
        with open(trace_file, "w") as f:
            json.dump(trace, f, indent=2)

    print(f"Saved first 100 individual traces to: {traces_dir}")

    # Generate summary statistics
    stats = {
        "total_traces": len(test_suite["test_traces"]),
        "total_events": test_suite["validation"]["total_events"],
        "unique_events": test_suite["validation"]["unique_events"],
        "time_range_ms": test_suite["validation"]["time_range_ms"],
        "generation_seed": args.seed,
    }

    stats_file = output_dir / "test_suite_stats.json"
    with open(stats_file, "w") as f:
        json.dump(stats, f, indent=2)

    print(f"Test suite statistics saved to: {stats_file}")


if __name__ == "__main__":
    main()
