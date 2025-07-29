#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Performance benchmark for sidecar watcher.
"""

import json
import subprocess
import time
import psutil
import statistics
from typing import List, Dict, Any
import argparse


def generate_test_actions(count: int) -> List[str]:
    """Generate test actions for benchmarking."""
    actions = []
    for i in range(count):
        if i % 3 == 0:
            action = {
                "action": "SendEmail",
                "score": 0.05,
                "payload": f"test{i}@example.com",
            }
        else:
            action = {"action": "LogSpend", "usd": 10.0, "payload": f"test{i}"}
        actions.append(json.dumps(action))
    return actions


def measure_processing_time(actions: List[str]) -> List[float]:
    """Measure processing time for each action."""
    times = []

    # Start sidecar watcher process
    process = subprocess.Popen(
        ["cargo", "run", "--bin", "sidecar-watcher"],
        cwd="runtime/sidecar-watcher",
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env={
            **subprocess.os.environ,
            "SPEC_SIG": "benchmark-test",
            "LIMIT_BUDGET": "1000.0",
            "LIMIT_SPAMSCORE": "0.07",
        },
    )

    try:
        # Send actions and measure time
        for action in actions:
            start_time = time.perf_counter()
            process.stdin.write(action + "\n")
            process.stdin.flush()
            end_time = time.perf_counter()
            times.append((end_time - start_time) * 1_000_000)  # Convert to microseconds

        # Close stdin to signal end
        process.stdin.close()

        # Wait for process to finish
        process.wait(timeout=10)

    except subprocess.TimeoutExpired:
        process.kill()
        raise RuntimeError("Sidecar watcher process timed out")

    return times


def get_memory_usage() -> int:
    """Get current memory usage in MB."""
    process = psutil.Process()
    return process.memory_info().rss // (1024 * 1024)


def run_benchmark(action_count: int = 1_000_000) -> Dict[str, Any]:
    """Run the benchmark and return results."""
    print(f"Generating {action_count} test actions...")
    actions = generate_test_actions(action_count)

    print("Starting sidecar watcher...")
    start_memory = get_memory_usage()

    print("Measuring processing times...")
    times = measure_processing_time(actions)

    end_memory = get_memory_usage()
    memory_used = end_memory - start_memory

    # Calculate statistics
    median_latency = statistics.median(times)
    mean_latency = statistics.mean(times)
    p95_latency = statistics.quantiles(times, n=20)[18]  # 95th percentile

    results = {
        "action_count": action_count,
        "median_latency_us": median_latency,
        "mean_latency_us": mean_latency,
        "p95_latency_us": p95_latency,
        "memory_mb": memory_used,
        "timestamp": time.time(),
    }

    print(f"Results:")
    print(f"  Median latency: {median_latency:.2f} µs")
    print(f"  Mean latency: {mean_latency:.2f} µs")
    print(f"  95th percentile: {p95_latency:.2f} µs")
    print(f"  Memory usage: {memory_used} MB")

    return results


def main():
    parser = argparse.ArgumentParser(
        description="Benchmark sidecar watcher performance"
    )
    parser.add_argument(
        "--count", type=int, default=1_000_000, help="Number of actions to test"
    )
    parser.add_argument("--output", help="Output JSON file for results")
    args = parser.parse_args()

    try:
        results = run_benchmark(args.count)

        if args.output:
            with open(args.output, "w") as f:
                json.dump(results, f, indent=2)
            print(f"Results saved to {args.output}")

        # Check performance thresholds
        if results["median_latency_us"] > 150:
            print("❌ Median latency exceeds 150 µs threshold")
            exit(1)

        if results["memory_mb"] > 50:
            print("❌ Memory usage exceeds 50 MB threshold")
            exit(1)

        print("✅ Performance within acceptable limits")

    except Exception as e:
        print(f"❌ Benchmark failed: {e}")
        exit(1)


if __name__ == "__main__":
    main()
