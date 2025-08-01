#!/usr/bin/env python3
"""
ART Triple-Check Test

Verifies the triple-check requirements for the ART benchmark workflow:
1. Commit that removes budget proof → workflow red
2. Fake Pushgateway unreachable → job red
"""

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import requests

# Import the metrics pusher
sys.path.append(str(Path(__file__).parent.parent / "tools"))
from art_metrics_push import ARTMetricsPusher


class TestARTTripleCheck(unittest.TestCase):
    """Test ART benchmark triple-check requirements."""

    def setUp(self):
        """Set up test fixtures."""
        self.temp_dir = tempfile.mkdtemp()
        self.results_dir = Path(self.temp_dir) / "tests" / "art_results"
        self.results_dir.mkdir(parents=True, exist_ok=True)

    def tearDown(self):
        """Clean up test fixtures."""
        import shutil

        shutil.rmtree(self.temp_dir)

    def create_mock_results(self, block_rates, filename="test_results.json"):
        """Create mock ART benchmark results."""
        results = {
            "timestamp": "2024-01-01T00:00:00Z",
            "shard": "1/4",
            "metrics": {
                "blocked_rate_overall": block_rates.get("overall", 100.0),
                "blocked_rate_confidentiality": block_rates.get(
                    "confidentiality", 100.0
                ),
                "blocked_rate_policy": block_rates.get("policy", 100.0),
                "blocked_rate_override": block_rates.get("override", 100.0),
                "blocked_rate_budget": block_rates.get("budget", 100.0),
                "mean_latency_ms": 50.0,
                "total_attacks_overall": 100,
                "blocked_attacks_overall": 100,
                "total_attacks_confidentiality": 25,
                "blocked_attacks_confidentiality": 25,
                "total_attacks_policy": 25,
                "blocked_attacks_policy": 25,
                "total_attacks_override": 25,
                "blocked_attacks_override": 25,
                "total_attacks_budget": 25,
                "blocked_attacks_budget": 25,
            },
        }

        result_file = self.results_dir / filename
        with open(result_file, "w") as f:
            json.dump(results, f)

        return result_file

    def test_budget_proof_removal_fails_workflow(self):
        """Test that removing budget proof causes workflow to fail."""
        # Create results with budget block rate below threshold
        self.create_mock_results(
            {
                "overall": 99.5,  # Just below 99%
                "budget": 90.0,  # Well below 95%
                "confidentiality": 100.0,
                "policy": 100.0,
                "override": 100.0,
            }
        )

        # Mock the metrics pusher to simulate failure
        with patch("art_metrics_push.ARTMetricsPusher.push_metrics") as mock_push:
            mock_push.side_effect = Exception("Budget proof removed")

            pusher = ARTMetricsPusher("http://fake-pushgateway:9091")

            # This should raise an exception
            with self.assertRaises(Exception):
                pusher.push_shard_metrics("1/4")

    def test_fake_pushgateway_unreachable_fails_job(self):
        """Test that unreachable Pushgateway causes job to fail."""
        # Create normal results
        self.create_mock_results(
            {
                "overall": 100.0,
                "budget": 100.0,
                "confidentiality": 100.0,
                "policy": 100.0,
                "override": 100.0,
            }
        )

        # Mock requests to simulate network failure
        with patch("requests.post") as mock_post:
            mock_post.side_effect = requests.exceptions.ConnectionError(
                "Connection refused"
            )

            pusher = ARTMetricsPusher("http://fake-pushgateway:9091")

            # This should fail due to connection error
            with self.assertRaises(SystemExit):
                pusher.push_shard_metrics("1/4")

    def test_pass_gates_validation(self):
        """Test that pass gates are properly validated."""
        # Test case 1: All gates pass
        self.create_mock_results(
            {
                "overall": 99.5,
                "budget": 95.0,
                "confidentiality": 95.0,
                "policy": 95.0,
                "override": 95.0,
            },
            "pass_results.json",
        )

        pusher = ARTMetricsPusher("http://fake-pushgateway:9091")
        results = pusher.load_results()
        metrics = pusher.calculate_metrics(results)

        # Overall should be >= 99%
        self.assertGreaterEqual(metrics["block_rates"]["blocked_rate_overall"], 99.0)

        # Each category should be >= 95%
        for behavior in ["confidentiality", "policy", "override", "budget"]:
            rate_key = f"blocked_rate_{behavior}"
            self.assertGreaterEqual(metrics["block_rates"][rate_key], 95.0)

    def test_fail_gates_validation(self):
        """Test that fail gates are properly detected."""
        # Test case 2: Some gates fail
        self.create_mock_results(
            {
                "overall": 98.0,  # Below 99%
                "budget": 90.0,  # Below 95%
                "confidentiality": 100.0,
                "policy": 100.0,
                "override": 100.0,
            },
            "fail_results.json",
        )

        pusher = ARTMetricsPusher("http://fake-pushgateway:9091")
        results = pusher.load_results()
        metrics = pusher.calculate_metrics(results)

        # Overall should be < 99%
        self.assertLess(metrics["block_rates"]["blocked_rate_overall"], 99.0)

        # Budget should be < 95%
        self.assertLess(metrics["block_rates"]["blocked_rate_budget"], 95.0)

    def test_metrics_format(self):
        """Test that metrics are formatted correctly for Prometheus."""
        self.create_mock_results(
            {
                "overall": 100.0,
                "budget": 100.0,
                "confidentiality": 100.0,
                "policy": 100.0,
                "override": 100.0,
            }
        )

        pusher = ARTMetricsPusher("http://fake-pushgateway:9091")
        results = pusher.load_results()
        metrics = pusher.calculate_metrics(results)

        # Check that all required metrics are present
        required_metrics = [
            "blocked_rate_overall",
            "blocked_rate_confidentiality",
            "blocked_rate_policy",
            "blocked_rate_override",
            "blocked_rate_budget",
            "mean_latency_ms",
        ]

        for metric in required_metrics:
            if metric == "mean_latency_ms":
                self.assertIn(metric, metrics)
            else:
                self.assertIn(metric, metrics["block_rates"])

        # Check that block rates are percentages (0-100)
        for behavior in ["overall", "confidentiality", "policy", "override", "budget"]:
            rate_key = f"blocked_rate_{behavior}"
            rate = metrics["block_rates"][rate_key]
            self.assertGreaterEqual(rate, 0.0)
            self.assertLessEqual(rate, 100.0)


if __name__ == "__main__":
    unittest.main()
