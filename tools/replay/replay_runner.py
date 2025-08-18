#!/usr/bin/env python3
"""
Replay Runner Tool for Testing Replay Determinism

This tool runs replay sessions multiple times to verify deterministic execution
and detect drift between runs.
"""

import json
import time
import hashlib
import argparse
import subprocess
import tempfile
import os
import sys
from pathlib import Path
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass
import statistics


@dataclass
class ReplayRun:
    """Represents a single replay run"""

    run_id: str
    start_time: float
    end_time: float
    events_processed: int
    chunks_generated: int
    drift_measurements: List[Dict[str, Any]]
    output_hash: str
    exit_code: int
    stdout: str
    stderr: str


@dataclass
class ReplayComparison:
    """Represents comparison between replay runs"""

    run1_id: str
    run2_id: str
    byte_identical: bool
    redaction_equivalent: bool
    drift_detected: bool
    differences: List[str]


class ReplayRunner:
    """Manages replay execution and comparison"""

    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.runs: List[ReplayRun] = []
        self.comparisons: List[ReplayComparison] = []

    def run_replay_session(
        self, session_id: str, replay_config: Dict[str, Any]
    ) -> ReplayRun:
        """Execute a single replay session"""
        run_id = f"{session_id}_{int(time.time() * 1000)}"
        start_time = time.time()

        # Create temporary replay configuration file
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            json.dump(replay_config, f, indent=2)
            config_file = f.name

        try:
            # Execute replay command
            cmd = [
                "cargo",
                "run",
                "-p",
                "sidecar-watcher",
                "--bin",
                "replay",
                "--",
                "--config",
                config_file,
                "--session-id",
                session_id,
                "--output-format",
                "json",
            ]

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.config.get("timeout_seconds", 300),
            )

            end_time = time.time()

            # Parse output
            output_data = self._parse_replay_output(result.stdout)

            # Generate output hash for determinism checking
            output_hash = hashlib.sha256(result.stdout.encode()).hexdigest()

            run = ReplayRun(
                run_id=run_id,
                start_time=start_time,
                end_time=end_time,
                events_processed=output_data.get("events_processed", 0),
                chunks_generated=output_data.get("chunks_generated", 0),
                drift_measurements=output_data.get("drift_measurements", []),
                output_hash=output_hash,
                exit_code=result.returncode,
                stdout=result.stdout,
                stderr=result.stderr,
            )

            self.runs.append(run)
            return run

        finally:
            # Clean up temporary file
            os.unlink(config_file)

    def _parse_replay_output(self, stdout: str) -> Dict[str, Any]:
        """Parse replay command output"""
        try:
            # Try to parse as JSON
            lines = stdout.strip().split("\n")
            for line in reversed(lines):
                if line.strip():
                    return json.loads(line)
        except (json.JSONDecodeError, IndexError):
            pass

        # Fallback parsing
        return {"events_processed": 0, "chunks_generated": 0, "drift_measurements": []}

    def run_multiple_replays(
        self, session_id: str, replay_config: Dict[str, Any], count: int
    ) -> List[ReplayRun]:
        """Run multiple replay sessions for the same configuration"""
        runs = []

        print(f"Running {count} replay sessions for {session_id}...")

        for i in range(count):
            print(f"  Run {i+1}/{count}...")
            run = self.run_replay_session(session_id, replay_config)
            runs.append(run)

            # Small delay between runs
            time.sleep(0.1)

        return runs

    def compare_runs(self, run1: ReplayRun, run2: ReplayRun) -> ReplayComparison:
        """Compare two replay runs"""
        differences = []

        # Check byte-level identity
        byte_identical = run1.output_hash == run2.output_hash

        # Check event count consistency
        if run1.events_processed != run2.events_processed:
            differences.append(
                f"Event count mismatch: {run1.events_processed} vs {run2.events_processed}"
            )

        # Check chunk count consistency
        if run1.chunks_generated != run2.chunks_generated:
            differences.append(
                f"Chunk count mismatch: {run1.chunks_generated} vs {run2.chunks_generated}"
            )

        # Check for drift
        drift_detected = bool(run1.drift_measurements) or bool(run2.drift_measurements)

        # Check redaction-equivalent view (simplified)
        redaction_equivalent = (
            run1.events_processed == run2.events_processed
            and run1.chunks_generated == run2.chunks_generated
        )

        comparison = ReplayComparison(
            run1_id=run1.run_id,
            run2_id=run2.run_id,
            byte_identical=byte_identical,
            redaction_equivalent=redaction_equivalent,
            drift_detected=drift_detected,
            differences=differences,
        )

        self.comparisons.append(comparison)
        return comparison

    def compare_all_runs(self) -> List[ReplayComparison]:
        """Compare all runs pairwise"""
        comparisons = []

        for i in range(len(self.runs)):
            for j in range(i + 1, len(self.runs)):
                comparison = self.compare_runs(self.runs[i], self.runs[j])
                comparisons.append(comparison)

        return comparisons

    def generate_report(self) -> Dict[str, Any]:
        """Generate comprehensive replay report"""
        if not self.runs:
            return {"error": "No runs to report"}

        # Calculate statistics
        run_durations = [run.end_time - run.start_time for run in self.runs]
        event_counts = [run.events_processed for run in self.runs]
        chunk_counts = [run.chunks_generated for run in self.runs]

        # Check determinism
        byte_identical_runs = sum(1 for comp in self.comparisons if comp.byte_identical)
        total_comparisons = len(self.comparisons)
        determinism_rate = (
            byte_identical_runs / total_comparisons if total_comparisons > 0 else 0
        )

        # Drift analysis
        drift_runs = sum(1 for run in self.runs if run.drift_measurements)
        drift_rate = drift_runs / len(self.runs) if self.runs else 0

        report = {
            "summary": {
                "total_runs": len(self.runs),
                "total_comparisons": total_comparisons,
                "determinism_rate": determinism_rate,
                "drift_rate": drift_rate,
                "byte_identical_comparisons": byte_identical_runs,
            },
            "statistics": {
                "run_duration": {
                    "mean": statistics.mean(run_durations) if run_durations else 0,
                    "median": statistics.median(run_durations) if run_durations else 0,
                    "min": min(run_durations) if run_durations else 0,
                    "max": max(run_durations) if run_durations else 0,
                    "std_dev": (
                        statistics.stdev(run_durations) if len(run_durations) > 1 else 0
                    ),
                },
                "events_processed": {
                    "mean": statistics.mean(event_counts) if event_counts else 0,
                    "median": statistics.median(event_counts) if event_counts else 0,
                    "min": min(event_counts) if event_counts else 0,
                    "max": max(event_counts) if event_counts else 0,
                    "std_dev": (
                        statistics.stdev(event_counts) if len(event_counts) > 1 else 0
                    ),
                },
                "chunks_generated": {
                    "mean": statistics.mean(chunk_counts) if chunk_counts else 0,
                    "median": statistics.median(chunk_counts) if chunk_counts else 0,
                    "min": min(chunk_counts) if chunk_counts else 0,
                    "max": max(chunk_counts) if chunk_counts else 0,
                    "std_dev": (
                        statistics.stdev(chunk_counts) if len(chunk_counts) > 1 else 0
                    ),
                },
            },
            "runs": [
                {
                    "run_id": run.run_id,
                    "start_time": run.start_time,
                    "end_time": run.end_time,
                    "duration": run.end_time - run.start_time,
                    "events_processed": run.events_processed,
                    "chunks_generated": run.chunks_generated,
                    "drift_measurements": len(run.drift_measurements),
                    "output_hash": run.output_hash,
                    "exit_code": run.exit_code,
                }
                for run in self.runs
            ],
            "comparisons": [
                {
                    "run1_id": comp.run1_id,
                    "run2_id": comp.run2_id,
                    "byte_identical": comp.byte_identical,
                    "redaction_equivalent": comp.redaction_equivalent,
                    "drift_detected": comp.drift_detected,
                    "differences": comp.differences,
                }
                for comp in self.comparisons
            ],
        }

        return report

    def save_report(self, output_file: str):
        """Save report to file"""
        report = self.generate_report()

        with open(output_file, "w") as f:
            json.dump(report, f, indent=2)

        print(f"Report saved to: {output_file}")

    def print_summary(self):
        """Print summary to console"""
        if not self.runs:
            print("No runs to summarize")
            return

        report = self.generate_report()
        summary = report["summary"]

        print("\n" + "=" * 60)
        print("REPLAY DETERMINISM SUMMARY")
        print("=" * 60)
        print(f"Total Runs: {summary['total_runs']}")
        print(f"Total Comparisons: {summary['total_comparisons']}")
        print(f"Determinism Rate: {summary['determinism_rate']:.2%}")
        print(f"Drift Rate: {summary['drift_rate']:.2%}")
        print(f"Byte-Identical Comparisons: {summary['byte_identical_comparisons']}")

        if summary["determinism_rate"] < 1.0:
            print("\n⚠️  NON-DETERMINISTIC EXECUTION DETECTED!")
            print("Some replay runs produced different outputs.")
        else:
            print("\n✅ DETERMINISTIC EXECUTION CONFIRMED!")
            print("All replay runs produced identical outputs.")

        if summary["drift_rate"] > 0:
            print(f"\n⚠️  DRIFT DETECTED IN {summary['drift_rate']:.1%} OF RUNS")

        # Show run details
        print("\n" + "-" * 60)
        print("INDIVIDUAL RUNS")
        print("-" * 60)

        for run_data in report["runs"]:
            print(
                f"Run {run_data['run_id']}: "
                f"{run_data['events_processed']} events, "
                f"{run_data['chunks_generated']} chunks, "
                f"{run_data['duration']:.3f}s"
            )

        # Show comparison details
        if self.comparisons:
            print("\n" + "-" * 60)
            print("RUN COMPARISONS")
            print("-" * 60)

            for comp in self.comparisons:
                status = "✅ IDENTICAL" if comp.byte_identical else "❌ DIFFERENT"
                print(f"{comp.run1_id} vs {comp.run2_id}: {status}")

                if not comp.byte_identical and comp.differences:
                    for diff in comp.differences:
                        print(f"  - {diff}")


def load_replay_config(config_file: str) -> Dict[str, Any]:
    """Load replay configuration from file"""
    with open(config_file, "r") as f:
        return json.load(f)


def create_default_config() -> Dict[str, Any]:
    """Create default replay configuration"""
    return {
        "chunk_bytes": 8192,
        "flush_ms": 100,
        "locale": "en_US.UTF-8",
        "timezone": "UTC",
        "seed": 42,
        "enable_drift_detection": True,
        "drift_threshold_ms": 50,
        "max_replay_attempts": 3,
        "timeout_seconds": 300,
    }


def main():
    parser = argparse.ArgumentParser(description="Replay Runner Tool")
    parser.add_argument("--config", "-c", help="Replay configuration file")
    parser.add_argument(
        "--session-id", "-s", default="test_session", help="Session ID for replay"
    )
    parser.add_argument(
        "--runs", "-r", type=int, default=3, help="Number of replay runs"
    )
    parser.add_argument(
        "--output", "-o", default="replay_report.json", help="Output report file"
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")

    args = parser.parse_args()

    # Load or create configuration
    if args.config:
        replay_config = load_replay_config(args.config)
    else:
        replay_config = create_default_config()

    # Create runner
    runner = ReplayRunner(replay_config)

    try:
        # Run multiple replays
        runs = runner.run_multiple_replays(args.session_id, replay_config, args.runs)

        # Compare all runs
        comparisons = runner.compare_all_runs()

        # Generate and save report
        runner.save_report(args.output)

        # Print summary
        runner.print_summary()

        # Exit with error code if non-deterministic
        report = runner.generate_report()
        if report.get("summary", {}).get("determinism_rate", 1.0) < 1.0:
            sys.exit(1)

    except KeyboardInterrupt:
        print("\nReplay execution interrupted by user")
        sys.exit(130)
    except Exception as e:
        print(f"Error during replay execution: {e}")
        if args.verbose:
            import traceback

            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
