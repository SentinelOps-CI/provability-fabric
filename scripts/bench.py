#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Performance benchmark for sidecar watcher.
"""

import json
import os
import subprocess
import tempfile
import time
import urllib.error
import urllib.request
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
                "spam_score": 0.05,
            }
        else:
            action = {"action": "LogSpend", "usd_amount": 10.0}
        actions.append(json.dumps(action))
    return actions


def _wait_for_sidecar_health(
    process: subprocess.Popen,
    log_path: str,
    timeout_s: float = 60,
) -> None:
    """Wait until the sidecar HTTP health endpoint responds."""
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        if process.poll() is not None:
            stderr = ""
            if process.stderr is not None:
                stderr = process.stderr.read().decode("utf-8", errors="replace")
            raise RuntimeError(
                f"Sidecar watcher exited early (code={process.returncode}). "
                f"stderr:\n{stderr[-4000:]}"
            )
        try:
            with urllib.request.urlopen("http://127.0.0.1:8006/health", timeout=1) as resp:
                if resp.status == 200:
                    return
        except (urllib.error.URLError, TimeoutError, OSError):
            time.sleep(0.2)
    stderr = ""
    if process.stderr is not None:
        stderr = process.stderr.read().decode("utf-8", errors="replace")
    raise RuntimeError(
        f"Sidecar watcher failed to start within {timeout_s:.0f}s "
        f"(log={log_path}). stderr:\n{stderr[-4000:]}"
    )


def _stop_sidecar(process: subprocess.Popen) -> None:
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def measure_processing_time(actions: List[str]) -> List[float]:
    """Measure log-write latency while the sidecar processes actions from LOG_FILE."""
    times = []

    with tempfile.NamedTemporaryFile(mode="w", delete=False, suffix=".log") as log_file:
        log_path = log_file.name

    bin_path = os.environ.get("SIDECAR_BIN")
    if bin_path:
        if not os.path.isfile(bin_path):
            raise RuntimeError(f"SIDECAR_BIN not found: {bin_path}")
        if not os.access(bin_path, os.X_OK):
            raise RuntimeError(f"SIDECAR_BIN not executable: {bin_path}")
        cmd = [bin_path]
        cwd = None
    else:
        cmd = ["cargo", "run", "--release", "--bin", "sidecar-watcher"]
        cwd = "runtime/sidecar-watcher"

    process = subprocess.Popen(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env={
            **os.environ,
            "LOG_FILE": log_path,
            "SPEC_SIG": "benchmark-test",
            "LIMIT_BUDGET": "1000.0",
            "LIMIT_SPAMSCORE": "0.07",
            "ENABLE_HEARTBEAT": "0",
            "PORT": "8006",
        },
    )

    try:
        _wait_for_sidecar_health(process, log_path)

        with open(log_path, "a", encoding="utf-8") as log:
            for action in actions:
                start_time = time.perf_counter()
                log.write(action + "\n")
                log.flush()
                end_time = time.perf_counter()
                times.append((end_time - start_time) * 1_000_000)

        # Sidecar tails LOG_FILE on a 1s poll loop; allow time to ingest the batch.
        time.sleep(min(30, max(3, len(actions) / 200)))
    finally:
        _stop_sidecar(process)
        try:
            os.unlink(log_path)
        except OSError:
            pass

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
