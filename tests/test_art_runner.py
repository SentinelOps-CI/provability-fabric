#!/usr/bin/env python3
"""
Test ART Runner

Simple test to verify ART runner functionality.
"""

import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from tests.art_runner import ARTRunner


class TestARTRunner:
    """Test ART runner functionality."""

    def test_validate_environment_missing_dataset(self):
        """Test environment validation with missing dataset."""
        with tempfile.TemporaryDirectory() as temp_dir:
            runner = ARTRunner("1/1")
            runner.dataset_path = Path(temp_dir) / "nonexistent.jsonl"
            runner.compose_file = Path(__file__).parent / "art_runner.py"

            assert not runner.validate_environment()

    def test_validate_environment_missing_compose(self):
        """Test environment validation with missing compose file."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Create dummy dataset
            dataset_file = Path(temp_dir) / "art_dataset.jsonl"
            dataset_file.write_text('{"test": "data"}\n')

            runner = ARTRunner("1/1")
            runner.dataset_path = dataset_file
            runner.compose_file = Path(temp_dir) / "nonexistent.yaml"

            assert not runner.validate_environment()

    def test_validate_environment_success(self):
        """Test successful environment validation."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Create dummy dataset
            dataset_file = Path(temp_dir) / "art_dataset.jsonl"
            dataset_file.write_text('{"test": "data"}\n')

            # Create dummy compose file
            compose_file = Path(temp_dir) / "art-compose.yaml"
            compose_file.write_text("version: '3.8'\n")

            runner = ARTRunner("1/1")
            runner.dataset_path = dataset_file
            runner.compose_file = compose_file

            assert runner.validate_environment()

    def test_load_dataset_shard(self):
        """Test dataset shard loading."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Create test dataset with multiple entries
            dataset_file = Path(temp_dir) / "art_dataset.jsonl"
            dataset_content = "\n".join(
                [
                    '{"id": "1", "behavior": "confidentiality"}',
                    '{"id": "2", "behavior": "policy"}',
                    '{"id": "3", "behavior": "override"}',
                    '{"id": "4", "behavior": "budget"}',
                ]
            )
            dataset_file.write_text(dataset_content)

            runner = ARTRunner("1/2")  # First shard of 2
            runner.dataset_path = dataset_file

            entries = runner.load_dataset_shard()

            # Should get entries 1 and 3 (odd-numbered lines)
            assert len(entries) == 2
            assert entries[0]["id"] == "1"
            assert entries[1]["id"] == "3"

    def test_calculate_metrics(self):
        """Test metrics calculation."""
        runner = ARTRunner("1/1")

        results = {
            "total_attacks": 100,
            "blocked_attacks": 95,
            "latencies": [10, 15, 20, 25, 30],
            "behavior_stats": {
                "confidentiality": {"total": 50, "blocked": 48, "latencies": [10, 15]},
                "policy": {"total": 50, "blocked": 47, "latencies": [20, 25, 30]},
            },
        }

        metrics = runner.calculate_metrics(results)

        assert metrics["overall_block_rate"] == 95.0
        assert metrics["total_attacks"] == 100
        assert metrics["blocked_attacks"] == 95
        assert metrics["mean_latency_ms"] == 20.0
        assert metrics["behavior_rates"]["confidentiality"] == 96.0
        assert metrics["behavior_rates"]["policy"] == 94.0

    def test_check_latency_guard_pass(self):
        """Test latency guard with acceptable latency."""
        runner = ARTRunner("1/1")
        metrics = {"mean_latency_ms": 15.0}

        assert runner.check_latency_guard(metrics)

    def test_check_latency_guard_fail(self):
        """Test latency guard with excessive latency."""
        runner = ARTRunner("1/1")
        metrics = {"mean_latency_ms": 30.0}

        assert not runner.check_latency_guard(metrics)

    @patch("tests.art_runner.subprocess.run")
    @patch("tests.art_runner.requests.get")
    def test_start_services_success(self, mock_requests, mock_subprocess):
        """Test successful service startup."""
        mock_subprocess.return_value = MagicMock()
        mock_requests.return_value = MagicMock(status_code=200)

        runner = ARTRunner("1/1")
        runner.compose_file = Path("/tmp/test.yaml")

        assert runner.start_services()

    @patch("tests.art_runner.subprocess.run")
    def test_start_services_failure(self, mock_subprocess):
        """Test service startup failure."""
        mock_subprocess.side_effect = Exception("Docker error")

        runner = ARTRunner("1/1")
        runner.compose_file = Path("/tmp/test.yaml")

        assert not runner.start_services()

    def test_replay_attack_success(self):
        """Test successful attack replay."""
        with patch("tests.art_runner.requests.post") as mock_post:
            mock_response = MagicMock()
            mock_response.status_code = 200
            mock_response.json.return_value = {"decision": "blocked"}
            mock_post.return_value = mock_response

            runner = ARTRunner("1/1")
            entry = {"id": "test", "behavior": "confidentiality"}

            blocked, latency, decision = runner.replay_attack(entry)

            assert blocked is True
            assert latency > 0
            assert decision == "blocked"

    def test_replay_attack_error(self):
        """Test attack replay with error."""
        with patch("tests.art_runner.requests.post") as mock_post:
            mock_post.side_effect = Exception("Network error")

            runner = ARTRunner("1/1")
            entry = {"id": "test", "behavior": "confidentiality"}

            blocked, latency, decision = runner.replay_attack(entry)

            assert blocked is False
            assert latency > 0
            assert decision == "error"


if __name__ == "__main__":
    pytest.main([__file__])
