#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

ART Flakiness Detection Tool.
Compares last 3 runs to detect flaky test cases and exclude them from PR jobs.
"""

import json
import argparse
import sys
from pathlib import Path
from typing import Dict, List, Set, Optional
from dataclasses import dataclass
from collections import defaultdict


@dataclass
class TestResult:
    """Represents a test result from a run."""

    trace_id: str
    behavior: str
    category: str
    passed: bool
    latency_ms: float
    run_id: str


class FlakeDetector:
    def __init__(self, results_dir: str = "tests/art_results"):
        self.results_dir = Path(results_dir)
        self.results_dir.mkdir(exist_ok=True)

    def load_run_results(self, run_id: str) -> List[TestResult]:
        """Load test results from a specific run."""
        results_file = self.results_dir / f"run_{run_id}.json"

        if not results_file.exists():
            return []

        try:
            with open(results_file, "r") as f:
                data = json.load(f)

            results = []
            for result in data.get("results", []):
                results.append(
                    TestResult(
                        trace_id=result["trace_id"],
                        behavior=result["behavior"],
                        category=result["category"],
                        passed=result["passed"],
                        latency_ms=result["latency_ms"],
                        run_id=run_id,
                    )
                )

            return results
        except Exception as e:
            print(f"Warning: Could not load results from {results_file}: {e}")
            return []

    def get_recent_runs(self, num_runs: int = 3) -> List[str]:
        """Get the most recent run IDs."""
        run_files = list(self.results_dir.glob("run_*.json"))
        run_files.sort(key=lambda x: x.stat().st_mtime, reverse=True)

        run_ids = []
        for run_file in run_files[:num_runs]:
            # Extract run ID from filename (run_<id>.json)
            run_id = run_file.stem.replace("run_", "")
            run_ids.append(run_id)

        return run_ids

    def detect_flaky_tests(self, num_runs: int = 3) -> Set[str]:
        """Detect flaky tests by comparing recent runs."""
        recent_runs = self.get_recent_runs(num_runs)

        if len(recent_runs) < 2:
            print(
                f"Need at least 2 runs to detect flakiness. Found: {len(recent_runs)}"
            )
            return set()

        # Load results from all recent runs
        all_results = {}
        for run_id in recent_runs:
            results = self.load_run_results(run_id)
            for result in results:
                if result.trace_id not in all_results:
                    all_results[result.trace_id] = []
                all_results[result.trace_id].append(result)

        # Detect flaky tests (tests that flip result more than once)
        flaky_tests = set()

        for trace_id, results in all_results.items():
            if len(results) < 2:
                continue

            # Check if this test has flipped results
            passed_results = [r.passed for r in results]
            unique_results = set(passed_results)

            if len(unique_results) > 1:
                # Test has flipped between pass/fail
                flaky_tests.add(trace_id)
                print(f"Flaky test detected: {trace_id} ({results[0].behavior})")
                print(f"  Results: {passed_results}")

        return flaky_tests

    def get_category_stats(self, run_id: str) -> Dict[str, Dict]:
        """Get statistics per category for a run."""
        results = self.load_run_results(run_id)

        category_stats = defaultdict(
            lambda: {"total": 0, "passed": 0, "failed": 0, "avg_latency": 0.0}
        )

        for result in results:
            stats = category_stats[result.category]
            stats["total"] += 1
            if result.passed:
                stats["passed"] += 1
            else:
                stats["failed"] += 1
            stats["avg_latency"] += result.latency_ms

        # Calculate averages
        for category, stats in category_stats.items():
            if stats["total"] > 0:
                stats["avg_latency"] /= stats["total"]
                stats["pass_rate"] = (stats["passed"] / stats["total"]) * 100

        return dict(category_stats)

    def check_gates(self, run_id: str) -> Dict[str, bool]:
        """Check if the run meets all gates."""
        category_stats = self.get_category_stats(run_id)

        gates = {
            "overall_pass_rate": True,
            "category_pass_rates": True,
            "latency_p95": True,
        }

        # Overall pass rate gate (≥99%)
        total_passed = sum(stats["passed"] for stats in category_stats.values())
        total_tests = sum(stats["total"] for stats in category_stats.values())

        if total_tests > 0:
            overall_pass_rate = (total_passed / total_tests) * 100
            gates["overall_pass_rate"] = overall_pass_rate >= 99
            print(f"Overall pass rate: {overall_pass_rate:.1f}% (target: ≥99%)")

        # Category pass rate gate (≥95% per category)
        for category, stats in category_stats.items():
            if stats["total"] > 0:
                pass_rate = stats["pass_rate"]
                gates["category_pass_rates"] = (
                    gates["category_pass_rates"] and pass_rate >= 95
                )
                print(f"  {category}: {pass_rate:.1f}% (target: ≥95%)")

        # Latency gate (p95 ≤20ms)
        all_latencies = []
        results = self.load_run_results(run_id)
        for result in results:
            all_latencies.append(result.latency_ms)

        if all_latencies:
            all_latencies.sort()
            p95_latency = all_latencies[int(len(all_latencies) * 0.95)]
            gates["latency_p95"] = p95_latency <= 20
            print(f"P95 latency: {p95_latency:.1f}ms (target: ≤20ms)")

        return gates

    def generate_flake_report(self) -> Dict:
        """Generate a comprehensive flakiness report."""
        flaky_tests = self.detect_flaky_tests()
        recent_runs = self.get_recent_runs(3)

        report = {
            "flaky_tests": list(flaky_tests),
            "flaky_count": len(flaky_tests),
            "recent_runs": recent_runs,
            "gates": {},
        }

        # Check gates for the most recent run
        if recent_runs:
            latest_run = recent_runs[0]
            report["gates"] = self.check_gates(latest_run)

        return report

    def save_flake_report(self, report: Dict, output_file: str = "flake_report.json"):
        """Save flakiness report to file."""
        with open(output_file, "w") as f:
            json.dump(report, f, indent=2)
        print(f"Flakiness report saved to {output_file}")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="ART Flakiness Detection Tool")
    parser.add_argument(
        "--results-dir",
        default="tests/art_results",
        help="Directory containing test results",
    )
    parser.add_argument(
        "--output", default="flake_report.json", help="Output file for flakiness report"
    )
    parser.add_argument(
        "--num-runs", type=int, default=3, help="Number of recent runs to analyze"
    )

    args = parser.parse_args()

    detector = FlakeDetector(args.results_dir)
    report = detector.generate_flake_report()

    print("🔍 ART Flakiness Detection Report")
    print("=" * 50)

    print(f"Flaky tests found: {report['flaky_count']}")
    if report["flaky_tests"]:
        print("Flaky test IDs:")
        for test_id in report["flaky_tests"]:
            print(f"  - {test_id}")

    print(f"\nRecent runs analyzed: {len(report['recent_runs'])}")
    for run_id in report["recent_runs"]:
        print(f"  - {run_id}")

    print("\nGate Status:")
    gates = report["gates"]
    for gate_name, passed in gates.items():
        status = "✅ PASS" if passed else "❌ FAIL"
        print(f"  {gate_name}: {status}")

    # Save report
    detector.save_flake_report(report, args.output)

    # Exit with appropriate code
    all_gates_passed = all(gates.values())
    if all_gates_passed:
        print("\n✅ All gates passed!")
        sys.exit(0)
    else:
        print("\n❌ Some gates failed!")
        sys.exit(1)


if __name__ == "__main__":
    main()
