#!/usr/bin/env python3
"""
ART Metrics Push Tool

Pushes ART benchmark metrics to Prometheus Pushgateway for monitoring
and alerting. Supports individual shard metrics and aggregation.
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Dict, List, Optional

from prometheus_client import CollectorRegistry, Gauge, push_to_gateway


class ARTMetricsPusher:
    """Pushes ART benchmark metrics to Prometheus Pushgateway."""

    def __init__(self, pushgateway_url: str, job_name: str = "art-benchmark"):
        self.pushgateway_url = pushgateway_url.rstrip("/")
        self.job_name = job_name
        self.registry = CollectorRegistry()

        # Define metrics
        self.block_rate_gauge = Gauge(
            "art_block_rate",
            "ART benchmark block rate by behavior category",
            ["behavior", "shard"],
            registry=self.registry,
        )

        self.latency_gauge = Gauge(
            "art_latency_ms",
            "ART benchmark mean latency in milliseconds",
            ["shard"],
            registry=self.registry,
        )

        self.total_attacks_gauge = Gauge(
            "art_total_attacks",
            "Total number of attacks processed",
            ["behavior", "shard"],
            registry=self.registry,
        )

        self.blocked_attacks_gauge = Gauge(
            "art_blocked_attacks",
            "Number of attacks blocked",
            ["behavior", "shard"],
            registry=self.registry,
        )

    def load_results(self, shard: Optional[str] = None) -> List[Dict]:
        """Load ART benchmark results from files."""
        results_dir = Path("tests/art_results")

        if not results_dir.exists():
            print(f"Error: Results directory not found: {results_dir}")
            return []

        results = []
        if shard:
            # Convert shard format from "1/4" to "1_4" for filename matching
            shard_normalized = shard.replace("/", "_")
            pattern = f"*shard_{shard_normalized}*.json"
        else:
            pattern = "*.json"

        for result_file in results_dir.glob(pattern):
            try:
                with open(result_file, "r") as f:
                    data = json.load(f)
                    results.append(data)
            except (json.JSONDecodeError, IOError) as e:
                print(f"Warning: Could not load {result_file}: {e}")
                continue

        return results

    def calculate_metrics(self, results: List[Dict]) -> Dict:
        """Calculate metrics from ART benchmark results."""
        if not results:
            return {}

        # Initialize counters
        total_attacks = {
            "confidentiality": 0,
            "policy": 0,
            "override": 0,
            "budget": 0,
            "overall": 0,
        }

        blocked_attacks = {
            "confidentiality": 0,
            "policy": 0,
            "override": 0,
            "budget": 0,
            "overall": 0,
        }

        latencies = []

        # Aggregate results
        for result in results:
            if "metrics" not in result:
                continue

            metrics = result["metrics"]

            # Count attacks by behavior
            behaviors = ["confidentiality", "policy", "override", "budget"]
            for behavior in behaviors:
                total_key = f"total_attacks_{behavior}"
                blocked_key = f"blocked_attacks_{behavior}"
                if total_key in metrics:
                    total_attacks[behavior] += metrics[total_key]
                if blocked_key in metrics:
                    blocked_attacks[behavior] += metrics[blocked_key]

            # Overall counts
            if "total_attacks_overall" in metrics:
                total_attacks["overall"] += metrics["total_attacks_overall"]
            if "blocked_attacks_overall" in metrics:
                blocked_attacks["overall"] += metrics["blocked_attacks_overall"]

            # Collect latencies
            if "mean_latency_ms" in metrics:
                latencies.append(metrics["mean_latency_ms"])

        # Calculate block rates
        block_rates = {}
        behaviors = ["confidentiality", "policy", "override", "budget", "overall"]
        for behavior in behaviors:
            if total_attacks[behavior] > 0:
                rate = blocked_attacks[behavior] / total_attacks[behavior] * 100
                block_rates[f"blocked_rate_{behavior}"] = rate
            else:
                block_rates[f"blocked_rate_{behavior}"] = 0.0

        # Calculate mean latency
        mean_latency = sum(latencies) / len(latencies) if latencies else 0.0

        return {
            "block_rates": block_rates,
            "total_attacks": total_attacks,
            "blocked_attacks": blocked_attacks,
            "mean_latency_ms": mean_latency,
        }

    def push_metrics(self, metrics: Dict, shard: Optional[str] = None):
        """Push metrics to Prometheus Pushgateway."""
        if not metrics:
            print("Warning: No metrics to push")
            return

        shard_label = shard or "aggregated"

        try:
            # Push block rates
            for behavior in [
                "confidentiality",
                "policy",
                "override",
                "budget",
                "overall",
            ]:
                rate_key = f"blocked_rate_{behavior}"
                if rate_key in metrics["block_rates"]:
                    self.block_rate_gauge.labels(
                        behavior=behavior, shard=shard_label
                    ).set(metrics["block_rates"][rate_key])

                    print(
                        f"Pushed {behavior} block rate: {metrics['block_rates'][rate_key]:.2f}%"
                    )

            # Push latency
            if "mean_latency_ms" in metrics:
                self.latency_gauge.labels(shard=shard_label).set(
                    metrics["mean_latency_ms"]
                )
                print(f"Pushed mean latency: {metrics['mean_latency_ms']:.2f} ms")

            # Push attack counts
            for behavior in [
                "confidentiality",
                "policy",
                "override",
                "budget",
                "overall",
            ]:
                if behavior in metrics["total_attacks"]:
                    self.total_attacks_gauge.labels(
                        behavior=behavior, shard=shard_label
                    ).set(metrics["total_attacks"][behavior])

                if behavior in metrics["blocked_attacks"]:
                    self.blocked_attacks_gauge.labels(
                        behavior=behavior, shard=shard_label
                    ).set(metrics["blocked_attacks"][behavior])

            # Push to gateway
            push_to_gateway(
                self.pushgateway_url, job=self.job_name, registry=self.registry
            )

            print(f"✅ Successfully pushed metrics to {self.pushgateway_url}")

        except Exception as e:
            print(f"❌ Failed to push metrics: {e}")
            sys.exit(1)

    def aggregate_and_push(self):
        """Aggregate results from all shards and push metrics."""
        print("Aggregating ART benchmark results from all shards...")

        # Load all results
        results = self.load_results()

        if not results:
            print("❌ No results found to aggregate")
            sys.exit(1)

        # Calculate aggregated metrics
        metrics = self.calculate_metrics(results)

        if not metrics:
            print("❌ No metrics calculated from results")
            sys.exit(1)

        # Push aggregated metrics
        self.push_metrics(metrics)

        # Print summary
        print("\n📊 ART Benchmark Summary:")
        for behavior in ["confidentiality", "policy", "override", "budget", "overall"]:
            rate_key = f"blocked_rate_{behavior}"
            if rate_key in metrics["block_rates"]:
                print(
                    f"  {behavior.capitalize()}: {metrics['block_rates'][rate_key]:.2f}%"
                )

        print(f"  Mean Latency: {metrics['mean_latency_ms']:.2f} ms")

    def push_shard_metrics(self, shard: str):
        """Push metrics for a specific shard."""
        print(f"Pushing metrics for shard {shard}...")

        # Load shard results
        results = self.load_results(shard)

        if not results:
            print(f"❌ No results found for shard {shard}")
            sys.exit(1)

        # Calculate metrics
        metrics = self.calculate_metrics(results)

        if not metrics:
            print(f"❌ No metrics calculated for shard {shard}")
            sys.exit(1)

        # Push metrics
        self.push_metrics(metrics, shard)


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Push ART benchmark metrics to Prometheus"
    )
    parser.add_argument(
        "--pushgateway-url", required=True, help="Prometheus Pushgateway URL"
    )
    parser.add_argument(
        "--job-name", default="art-benchmark", help="Job name for Prometheus metrics"
    )
    parser.add_argument("--shard", help="Specific shard to process (e.g., '1/4')")
    parser.add_argument(
        "--aggregate", action="store_true", help="Aggregate results from all shards"
    )

    args = parser.parse_args()

    # Validate pushgateway URL
    if not args.pushgateway_url.startswith(("http://", "https://")):
        print("❌ Pushgateway URL must start with http:// or https://")
        sys.exit(1)

    # Create metrics pusher
    pusher = ARTMetricsPusher(args.pushgateway_url, args.job_name)

    if args.aggregate:
        pusher.aggregate_and_push()
    elif args.shard:
        pusher.push_shard_metrics(args.shard)
    else:
        print("❌ Must specify either --shard or --aggregate")
        sys.exit(1)


if __name__ == "__main__":
    main()
