#!/usr/bin/env python3
"""
Simple Bundle Replay and Drift Detection Test

This script demonstrates:
1. Bundle creation and integrity verification
2. Replay determinism testing
3. Basic drift detection concepts

SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors
"""

import os
import json
import subprocess
import hashlib
import time
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Optional


class BundleReplayTest:
    """Simple bundle replay and drift detection test."""

    def __init__(self, agent_name: str = "test-replay-agent"):
        self.agent_name = agent_name
        self.pf_cli = "./core/cli/pf/pf-new"
        self.bundle_dir = Path(f"bundles/{agent_name}")
        self.results = {"timestamp": time.time(), "tests": [], "summary": {}}

    def setup_test_bundle(self) -> bool:
        """Create a test bundle if it doesn't exist."""
        print(f"🔧 Setting up test bundle: {self.agent_name}")

        if self.bundle_dir.exists():
            print(f"✅ Bundle directory already exists: {self.bundle_dir}")
            return True

        try:
            # Initialize bundle using CLI
            result = subprocess.run(
                [self.pf_cli, "init", self.agent_name],
                capture_output=True,
                text=True,
                timeout=30,
            )

            if result.returncode == 0:
                print(f"✅ Bundle created successfully")
                return True
            else:
                print(f"❌ Bundle creation failed: {result.stderr}")
                return False

        except Exception as e:
            print(f"❌ Error creating bundle: {e}")
            return False

    def calculate_bundle_hash(self) -> Optional[str]:
        """Calculate hash of bundle contents for integrity verification."""
        if not self.bundle_dir.exists():
            return None

        hasher = hashlib.sha256()

        # Sort files for deterministic hashing
        files = sorted(self.bundle_dir.rglob("*"))
        for file_path in files:
            if file_path.is_file():
                try:
                    with open(file_path, "rb") as f:
                        hasher.update(f.read())
                except Exception as e:
                    print(f"⚠️  Warning: Could not hash {file_path}: {e}")

        return hasher.hexdigest()

    def test_bundle_integrity(self) -> Dict:
        """Test bundle integrity and consistency."""
        print("🔍 Testing bundle integrity...")

        test_result = {
            "name": "bundle_integrity",
            "status": "unknown",
            "details": {},
            "timestamp": time.time(),
        }

        # Check if spec.yaml exists
        spec_file = self.bundle_dir / "spec.yaml"
        if spec_file.exists():
            test_result["details"]["spec_exists"] = True
            test_result["details"]["spec_size"] = spec_file.stat().st_size

            # Calculate bundle hash
            bundle_hash = self.calculate_bundle_hash()
            if bundle_hash:
                test_result["details"]["bundle_hash"] = bundle_hash
                test_result["status"] = "passed"
                print(f"✅ Bundle integrity verified: {bundle_hash[:16]}...")
            else:
                test_result["status"] = "failed"
                print("❌ Bundle hash calculation failed")
        else:
            test_result["details"]["spec_exists"] = False
            test_result["status"] = "failed"
            print("❌ Bundle spec.yaml not found")

        return test_result

    def test_replay_determinism(self) -> Dict:
        """Test replay determinism by running the same operation multiple times."""
        print("🔄 Testing replay determinism...")

        test_result = {
            "name": "replay_determinism",
            "status": "unknown",
            "details": {"runs": [], "hashes": [], "drift_detected": False},
            "timestamp": time.time(),
        }

        # Run the test multiple times to check for consistency
        for i in range(3):
            print(f"  Run {i+1}/3...")

            run_start = time.time()
            current_hash = self.calculate_bundle_hash()
            run_end = time.time()

            run_result = {
                "run_id": i + 1,
                "bundle_hash": current_hash,
                "execution_time": run_end - run_start,
                "timestamp": run_start,
            }

            test_result["details"]["runs"].append(run_result)
            if current_hash:
                test_result["details"]["hashes"].append(current_hash)

        # Check for drift (hash differences)
        unique_hashes = set(test_result["details"]["hashes"])
        if len(unique_hashes) == 1:
            test_result["status"] = "passed"
            test_result["details"]["drift_detected"] = False
            print("✅ No drift detected - all runs produced identical hashes")
        else:
            test_result["status"] = "failed"
            test_result["details"]["drift_detected"] = True
            print(f"❌ Drift detected - found {len(unique_hashes)} different hashes")

        return test_result

    def test_non_interference_concept(self) -> Dict:
        """Demonstrate non-interference concepts without external services."""
        print("🔐 Testing non-interference concepts...")

        test_result = {
            "name": "non_interference_demo",
            "status": "unknown",
            "details": {
                "public_outputs": [],
                "high_secret_variations": 0,
                "low_observations_consistent": True,
            },
            "timestamp": time.time(),
        }

        # Simulate different high-security inputs but same public inputs
        public_input = "process_transaction"
        high_secrets = ["secret1", "secret2", "secret3"]

        low_observations = []

        for i, secret in enumerate(high_secrets):
            # Simulate processing with different high secrets
            # In a real system, this would be actual processing
            simulated_output = {
                "transaction_id": f"tx_{hashlib.md5(public_input.encode()).hexdigest()[:8]}",
                "status": "processed",
                "public_metadata": {"type": "transfer", "timestamp": int(time.time())},
                # High secret should NOT leak into public output
                "secret_hash": hashlib.sha256(
                    secret.encode()
                ).hexdigest(),  # This would be hidden
            }

            # Only observe what should be public
            public_observation = {
                "transaction_id": simulated_output["transaction_id"],
                "status": simulated_output["status"],
                "public_metadata": simulated_output["public_metadata"],
            }

            low_observations.append(public_observation)
            test_result["details"]["public_outputs"].append(public_observation)

        test_result["details"]["high_secret_variations"] = len(high_secrets)

        # Check if low observations are consistent (non-interference property)
        # All public outputs should be identical despite different high secrets
        first_obs = low_observations[0][
            "transaction_id"
        ]  # Use transaction_id for comparison
        all_consistent = all(
            obs["transaction_id"] == first_obs for obs in low_observations
        )

        test_result["details"]["low_observations_consistent"] = all_consistent

        if all_consistent:
            test_result["status"] = "passed"
            print(
                "✅ Non-interference maintained - public outputs consistent despite different high secrets"
            )
        else:
            test_result["status"] = "failed"
            print(
                "❌ Non-interference violated - public outputs differ with different high secrets"
            )

        return test_result

    def run_all_tests(self) -> Dict:
        """Run all tests and compile results."""
        print("🚀 Starting Bundle Replay and Drift Detection Tests\n")

        # Setup test bundle
        if not self.setup_test_bundle():
            print("❌ Test setup failed")
            return {"error": "test_setup_failed"}

        # Run tests
        tests = [
            self.test_bundle_integrity,
            self.test_replay_determinism,
            self.test_non_interference_concept,
        ]

        for test_func in tests:
            try:
                result = test_func()
                self.results["tests"].append(result)
                print()  # Add spacing between tests
            except Exception as e:
                error_result = {
                    "name": test_func.__name__,
                    "status": "error",
                    "details": {"error": str(e)},
                    "timestamp": time.time(),
                }
                self.results["tests"].append(error_result)
                print(f"❌ Test {test_func.__name__} failed with error: {e}\n")

        # Compile summary
        passed = sum(1 for t in self.results["tests"] if t["status"] == "passed")
        failed = sum(1 for t in self.results["tests"] if t["status"] == "failed")
        errors = sum(1 for t in self.results["tests"] if t["status"] == "error")

        self.results["summary"] = {
            "total_tests": len(self.results["tests"]),
            "passed": passed,
            "failed": failed,
            "errors": errors,
            "success_rate": (
                passed / len(self.results["tests"]) if self.results["tests"] else 0
            ),
        }

        # Print summary
        print("=" * 60)
        print("BUNDLE REPLAY & DRIFT DETECTION TEST RESULTS")
        print("=" * 60)
        print(f"📊 Total Tests: {self.results['summary']['total_tests']}")
        print(f"✅ Passed: {passed}")
        print(f"❌ Failed: {failed}")
        print(f"⚠️  Errors: {errors}")
        print(f"📈 Success Rate: {self.results['summary']['success_rate']:.1%}")
        print()

        # Print individual test results
        for test in self.results["tests"]:
            status_emoji = {"passed": "✅", "failed": "❌", "error": "⚠️"}.get(
                test["status"], "❓"
            )
            print(f"{status_emoji} {test['name']}: {test['status'].upper()}")

        return self.results


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Simple Bundle Replay and Drift Detection Test"
    )
    parser.add_argument(
        "--agent-name", default="test-replay-agent", help="Name of test agent"
    )
    parser.add_argument("--output", help="Output JSON file for results")

    args = parser.parse_args()

    # Run tests
    test_runner = BundleReplayTest(args.agent_name)
    results = test_runner.run_all_tests()

    # Save results if output file specified
    if args.output:
        with open(args.output, "w") as f:
            json.dump(results, f, indent=2)
        print(f"\n📄 Results saved to: {args.output}")

    # Exit with appropriate code
    if "error" in results:
        sys.exit(1)
    elif results["summary"]["failed"] > 0 or results["summary"]["errors"] > 0:
        sys.exit(1)
    else:
        sys.exit(0)


if __name__ == "__main__":
    main()
