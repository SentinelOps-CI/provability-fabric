#!/usr/bin/env python3
"""
ART Replay Harness

Replays ART dataset attacks through Provability-Fabric components and measures
block rates and latency. Supports sharded execution for parallel processing.
"""

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import Dict, List, Tuple

import requests


class ARTRunner:
    """ART benchmark replay harness."""

    def __init__(self, shard: str, timeout: int = 60):
        self.shard_parts = shard.split("/")
        self.shard_num = int(self.shard_parts[0])
        self.total_shards = int(self.shard_parts[1])
        self.timeout = timeout

        # Environment variables
        self.art_parallel = int(os.getenv("ART_PARALLEL", "1"))
        self.art_timeout = int(os.getenv("ART_TIMEOUT", "60"))
        self.proofmeter_url = os.getenv("PROOFMETER_URL", "http://localhost:8080")

        # Paths
        self.dataset_path = Path.home() / ".cache" / "art" / "art_dataset.jsonl"
        self.compose_file = Path("docker/art-compose.yaml")
        self.results_dir = Path("tests/art_results")

    def validate_environment(self) -> bool:
        """Validate required environment and files."""
        if not self.dataset_path.exists():
            print(f"Error: ART dataset not found at {self.dataset_path}")
            print("Run: python tools/art_fetch.py")
            return False

        if not self.compose_file.exists():
            print(f"Error: Docker compose file not found at {self.compose_file}")
            return False

        # Create results directory
        self.results_dir.mkdir(parents=True, exist_ok=True)

        return True

    def load_dataset_shard(self) -> List[Dict]:
        """Load dataset entries for this shard."""
        entries = []

        with open(self.dataset_path, "r") as f:
            for line_num, line in enumerate(f, 1):
                # Shard by line number
                if (line_num - 1) % self.total_shards == (self.shard_num - 1):
                    try:
                        entry = json.loads(line.strip())
                        entries.append(entry)
                    except json.JSONDecodeError:
                        continue

        print(
            f"Loaded {len(entries)} entries for shard {self.shard_num}/{self.total_shards}"
        )
        return entries

    def start_services(self) -> bool:
        """Start ART docker compose services."""
        try:
            print("Starting ART services...")

            # Start services
            subprocess.run(
                ["docker", "compose", "-f", str(self.compose_file), "up", "-d"],
                check=True,
            )

            # Wait for services to be ready
            print("Waiting for services to be ready...")
            for service in ["agent", "watcher", "proofmeter"]:
                for attempt in range(30):
                    try:
                        if service == "agent":
                            # Check agent health
                            response = requests.get(
                                "http://localhost:3000/health", timeout=5
                            )
                        elif service == "watcher":
                            # Check watcher health
                            response = requests.get(
                                "http://localhost:3001/health", timeout=5
                            )
                        elif service == "proofmeter":
                            # Check ProofMeter health
                            response = requests.get(
                                f"{self.proofmeter_url}/health", timeout=5
                            )

                        if response.status_code == 200:
                            print(f"✓ {service} ready")
                            break
                    except requests.RequestException:
                        if attempt == 29:
                            print(f"✗ {service} failed to start")
                            return False
                        time.sleep(1)

            return True

        except subprocess.CalledProcessError as e:
            print(f"Error starting services: {e}")
            return False

    def stop_services(self):
        """Stop ART docker compose services."""
        try:
            subprocess.run(
                ["docker", "compose", "-f", str(self.compose_file), "down"], check=True
            )
        except subprocess.CalledProcessError as e:
            print(f"Warning: Error stopping services: {e}")

    def replay_attack(self, entry: Dict) -> Tuple[bool, float, str]:
        """Replay a single ART attack and measure results."""
        start_time = time.time()

        try:
            # Prepare attack payload
            payload = {
                "system_prompt": entry.get("system_prompt", ""),
                "user_prompt": entry.get("user_prompt", ""),
                "tools": entry.get("tools", []),
                "attack_id": entry.get("id", "unknown"),
                "behavior": entry.get("behavior", "unknown"),
            }

            # Send to agent
            response = requests.post(
                "http://localhost:3000/process", json=payload, timeout=self.timeout
            )

            latency_ms = (time.time() - start_time) * 1000

            if response.status_code == 200:
                result = response.json()
                decision = result.get("decision", "unknown")
                blocked = decision in ["blocked", "rejected", "violation"]
                return blocked, latency_ms, decision
            else:
                print(f"Warning: Agent returned {response.status_code}")
                return False, latency_ms, "error"

        except requests.RequestException as e:
            latency_ms = (time.time() - start_time) * 1000
            print(f"Error replaying attack: {e}")
            return False, latency_ms, "error"

    def run_benchmark(self, entries: List[Dict]) -> Dict:
        """Run ART benchmark on dataset entries."""
        results = {
            "total_attacks": len(entries),
            "blocked_attacks": 0,
            "latencies": [],
            "decisions": {},
            "behavior_stats": {},
            "errors": [],
        }

        print(f"Running benchmark on {len(entries)} attacks...")

        for i, entry in enumerate(entries, 1):
            if i % 100 == 0:
                print(f"Progress: {i}/{len(entries)}")

            behavior = entry.get("behavior", "unknown")
            attack_id = entry.get("id", f"attack_{i}")

            blocked, latency, decision = self.replay_attack(entry)

            # Record results
            if blocked:
                results["blocked_attacks"] += 1

            results["latencies"].append(latency)
            results["decisions"][attack_id] = decision

            # Track by behavior
            if behavior not in results["behavior_stats"]:
                results["behavior_stats"][behavior] = {
                    "total": 0,
                    "blocked": 0,
                    "latencies": [],
                }

            results["behavior_stats"][behavior]["total"] += 1
            if blocked:
                results["behavior_stats"][behavior]["blocked"] += 1
            results["behavior_stats"][behavior]["latencies"].append(latency)

            # Check latency guard
            if latency > 25:
                results["errors"].append(
                    f"Attack {attack_id} exceeded 25ms latency: {latency:.2f}ms"
                )

        return results

    def calculate_metrics(self, results: Dict) -> Dict:
        """Calculate benchmark metrics."""
        total = results["total_attacks"]
        blocked = results["blocked_attacks"]

        metrics = {
            "overall_block_rate": (blocked / total * 100) if total > 0 else 0,
            "mean_latency_ms": (
                sum(results["latencies"]) / len(results["latencies"])
                if results["latencies"]
                else 0
            ),
            "p95_latency_ms": (
                sorted(results["latencies"])[int(len(results["latencies"]) * 0.95)]
                if results["latencies"]
                else 0
            ),
            "total_attacks": total,
            "blocked_attacks": blocked,
            "behavior_rates": {},
        }

        # Calculate block rates by behavior
        for behavior, stats in results["behavior_stats"].items():
            if stats["total"] > 0:
                metrics["behavior_rates"][behavior] = (
                    stats["blocked"] / stats["total"]
                ) * 100
            else:
                metrics["behavior_rates"][behavior] = 0

        return metrics

    def save_results(self, results: Dict, metrics: Dict):
        """Save benchmark results to file."""
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        shard_suffix = f"shard_{self.shard_num}_of_{self.total_shards}"

        # Save detailed results
        results_file = self.results_dir / f"art_results_{timestamp}_{shard_suffix}.json"
        with open(results_file, "w") as f:
            json.dump(
                {
                    "results": results,
                    "metrics": metrics,
                    "timestamp": timestamp,
                    "shard": f"{self.shard_num}/{self.total_shards}",
                },
                f,
                indent=2,
            )

        # Save metrics summary
        metrics_file = self.results_dir / f"art_metrics_{timestamp}_{shard_suffix}.json"
        with open(metrics_file, "w") as f:
            json.dump(metrics, f, indent=2)

        print(f"Results saved to {results_file}")
        print(f"Metrics saved to {metrics_file}")

    def check_latency_guard(self, metrics: Dict) -> bool:
        """Check if mean latency exceeds 25ms guard."""
        if metrics["mean_latency_ms"] > 25:
            print(
                f"✗ Mean latency {metrics['mean_latency_ms']:.2f}ms exceeds 25ms guard"
            )
            return False
        else:
            print(
                f"✓ Mean latency {metrics['mean_latency_ms']:.2f}ms within 25ms guard"
            )
            return True

    def run(self) -> bool:
        """Run ART benchmark."""
        try:
            # Validate environment
            if not self.validate_environment():
                return False

            # Load dataset shard
            entries = self.load_dataset_shard()
            if not entries:
                print("No entries found for this shard")
                return False

            # Start services
            if not self.start_services():
                return False

            try:
                # Run benchmark
                results = self.run_benchmark(entries)

                # Calculate metrics
                metrics = self.calculate_metrics(results)

                # Save results
                self.save_results(results, metrics)

                # Print summary
                print("\n=== ART Benchmark Results ===")
                print(f"Total Attacks: {metrics['total_attacks']}")
                print(f"Blocked Attacks: {metrics['blocked_attacks']}")
                print(f"Overall Block Rate: {metrics['overall_block_rate']:.2f}%")
                print(f"Mean Latency: {metrics['mean_latency_ms']:.2f}ms")
                print(f"P95 Latency: {metrics['p95_latency_ms']:.2f}ms")

                print("\nBlock Rates by Behavior:")
                for behavior, rate in metrics["behavior_rates"].items():
                    print(f"  {behavior}: {rate:.2f}%")

                # Check latency guard
                if not self.check_latency_guard(metrics):
                    return False

                return True

            finally:
                # Stop services
                self.stop_services()

        except Exception as e:
            print(f"Error running ART benchmark: {e}")
            return False


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="ART Replay Harness")
    parser.add_argument("--shard", required=True, help="Shard in format N/total")
    parser.add_argument(
        "--timeout", type=int, default=60, help="Request timeout in seconds"
    )
    parser.add_argument("--attack-id", help="Run single attack by ID")

    args = parser.parse_args()

    # Validate shard format
    try:
        shard_parts = args.shard.split("/")
        if len(shard_parts) != 2:
            raise ValueError("Shard must be in format N/total")
        int(shard_parts[0])
        int(shard_parts[1])
    except (ValueError, IndexError):
        print("Error: Shard must be in format N/total (e.g., 1/4)")
        sys.exit(1)

    # Run benchmark
    runner = ARTRunner(args.shard, args.timeout)
    success = runner.run()

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    import os

    main()
