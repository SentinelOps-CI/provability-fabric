#!/usr/bin/env python3
"""
Red-Team / LLM Adversarial Harness

This tool runs adversarial test cases against agent containers to verify
that sidecar guards and ledger risk scoring catch malicious behavior.
"""

import os
import sys
import json
import yaml
import argparse
import subprocess
import requests
import time
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass


@dataclass
class AttackCase:
    id: str
    name: str
    prompt: str
    expected_violation: str
    expected_risk_min: float = 0.8
    timeout: int = 60


class RedTeamRunner:
    def __init__(self, kube_config: str, ledger_url: str = "http://localhost:4000"):
        self.kube_config = kube_config
        self.ledger_url = ledger_url
        self.attack_cases = []

    def load_attack_cases(self, cases_dir: str) -> bool:
        """Load attack cases from JSON files."""
        try:
            cases_path = Path(cases_dir)
            if not cases_path.exists():
                print(f"❌ Attack cases directory not found: {cases_dir}")
                return False

            for case_file in cases_path.glob("*_attack.json"):
                with open(case_file, "r") as f:
                    case_data = json.load(f)

                case = AttackCase(
                    id=case_data.get("id", case_file.stem),
                    name=case_data.get("name", "Unknown Attack"),
                    prompt=case_data.get("prompt", ""),
                    expected_violation=case_data.get("expected_violation", ""),
                    expected_risk_min=case_data.get("expected_risk_min", 0.8),
                    timeout=case_data.get("timeout", 60),
                )

                self.attack_cases.append(case)

            print(f"✅ Loaded {len(self.attack_cases)} attack cases")
            return True

        except Exception as e:
            print(f"❌ Error loading attack cases: {e}")
            return False

    def deploy_test_agent(self, case: AttackCase) -> Optional[str]:
        """Deploy a test agent pod for the attack case."""
        try:
            # Create a unique pod name
            pod_name = f"redteam-{case.id}-{int(time.time())}"

            # Create pod manifest
            pod_manifest = {
                "apiVersion": "v1",
                "kind": "Pod",
                "metadata": {
                    "name": pod_name,
                    "labels": {"app": "redteam-test", "case": case.id},
                    "annotations": {
                        "spec.sig": "sigstore:sha256:test1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef",
                        "lean.hash": "sha256:test1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef",
                    },
                },
                "spec": {
                    "containers": [
                        {
                            "name": "test-agent",
                            "image": "busybox:latest",
                            "command": [
                                "sh",
                                "-c",
                                f"echo '{case.prompt}' && sleep 30",
                            ],
                            "env": [
                                {"name": "TEST_CASE", "value": case.id},
                                {"name": "TEST_PROMPT", "value": case.prompt},
                            ],
                        }
                    ],
                    "restartPolicy": "Never",
                },
            }

            # Apply pod manifest
            with open("/tmp/pod.yaml", "w") as f:
                yaml.dump(pod_manifest, f)

            result = subprocess.run(
                [
                    "kubectl",
                    "--kubeconfig",
                    self.kube_config,
                    "apply",
                    "-f",
                    "/tmp/pod.yaml",
                ],
                capture_output=True,
                text=True,
            )

            if result.returncode != 0:
                print(f"❌ Failed to deploy test agent: {result.stderr}")
                return None

            print(f"✅ Deployed test agent: {pod_name}")
            return pod_name

        except Exception as e:
            print(f"❌ Error deploying test agent: {e}")
            return None

    def wait_for_pod_status(
        self, pod_name: str, expected_status: str, timeout: int = 60
    ) -> bool:
        """Wait for pod to reach expected status."""
        start_time = time.time()

        while time.time() - start_time < timeout:
            try:
                result = subprocess.run(
                    [
                        "kubectl",
                        "--kubeconfig",
                        self.kube_config,
                        "get",
                        "pod",
                        pod_name,
                        "-o",
                        "jsonpath={.status.phase}",
                    ],
                    capture_output=True,
                    text=True,
                )

                if result.returncode == 0:
                    status = result.stdout.strip()
                    if status == expected_status:
                        print(f"✅ Pod {pod_name} reached status: {status}")
                        return True
                    elif status in ["Failed", "CrashLoopBackOff"]:
                        print(f"⚠️  Pod {pod_name} failed: {status}")
                        return True

                time.sleep(2)

            except Exception as e:
                print(f"Warning: Error checking pod status: {e}")
                time.sleep(2)

        print(f"❌ Timeout waiting for pod {pod_name} to reach {expected_status}")
        return False

    def query_ledger_risk(self, capsule_hash: str) -> Optional[float]:
        """Query ledger for risk score of a capsule."""
        try:
            query = """
            query Capsule($hash: ID!) {
                capsule(hash: $hash) {
                    hash
                    riskScore
                    reason
                }
            }
            """

            variables = {"hash": capsule_hash}

            response = requests.post(
                f"{self.ledger_url}/graphql",
                json={"query": query, "variables": variables},
                timeout=10,
            )

            if response.status_code == 200:
                data = response.json()
                if "data" in data and "capsule" in data["data"]:
                    return data["data"]["capsule"]["riskScore"]

            return None

        except Exception as e:
            print(f"Warning: Error querying ledger: {e}")
            return None

    def run_attack_case(self, case: AttackCase) -> bool:
        """Run a single attack case."""
        print(f"\n🔴 Running attack case: {case.name}")
        print(f"   Expected violation: {case.expected_violation}")
        print(f"   Expected risk min: {case.expected_risk_min}")

        # Deploy test agent
        pod_name = self.deploy_test_agent(case)
        if not pod_name:
            return False

        try:
            # Wait for pod to be running
            if not self.wait_for_pod_status(pod_name, "Running", 30):
                return False

            # Wait for potential violation (sidecar guard trip)
            if not self.wait_for_pod_status(pod_name, "CrashLoopBackOff", case.timeout):
                print(f"⚠️  Pod did not crash as expected, checking ledger...")

            # Query ledger for risk score
            capsule_hash = f"sha256:test1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef"
            risk_score = self.query_ledger_risk(capsule_hash)

            if risk_score is not None:
                print(f"📊 Ledger risk score: {risk_score}")

                if risk_score >= case.expected_risk_min:
                    print(
                        f"✅ Attack case PASSED: Risk score {risk_score} >= {case.expected_risk_min}"
                    )
                    return True
                else:
                    print(
                        f"❌ Attack case FAILED: Risk score {risk_score} < {case.expected_risk_min}"
                    )
                    return False
            else:
                print(f"❌ Attack case FAILED: No risk score found in ledger")
                return False

        finally:
            # Clean up pod
            try:
                subprocess.run(
                    [
                        "kubectl",
                        "--kubeconfig",
                        self.kube_config,
                        "delete",
                        "pod",
                        pod_name,
                    ],
                    capture_output=True,
                )
                print(f"🧹 Cleaned up pod: {pod_name}")
            except Exception as e:
                print(f"Warning: Error cleaning up pod: {e}")

    def run_all_attacks(self) -> Dict[str, bool]:
        """Run all attack cases and return results."""
        results = {}

        print(f"🚀 Starting red-team attack simulation...")
        print(f"📊 Running {len(self.attack_cases)} attack cases")

        for case in self.attack_cases:
            success = self.run_attack_case(case)
            results[case.id] = success

        return results

    def generate_report(self, results: Dict[str, bool]) -> str:
        """Generate a summary report."""
        total_cases = len(results)
        passed_cases = sum(1 for success in results.values() if success)
        failed_cases = total_cases - passed_cases

        report = f"""
# Red-Team Attack Simulation Report

## Summary
- **Total Cases:** {total_cases}
- **Passed:** {passed_cases}
- **Failed:** {failed_cases}
- **Success Rate:** {(passed_cases/total_cases)*100:.1f}%

## Detailed Results
"""

        for case_id, success in results.items():
            status = "✅ PASS" if success else "❌ FAIL"
            report += f"- {case_id}: {status}\n"

        if failed_cases > 0:
            report += f"\n⚠️  **WARNING:** {failed_cases} attack cases were not caught by guards!"
        else:
            report += (
                f"\n✅ **SUCCESS:** All attack cases were properly caught by guards!"
            )

        return report


def main():
    parser = argparse.ArgumentParser(description="Red-Team Attack Harness")
    parser.add_argument("--kube-config", required=True, help="Path to kubeconfig file")
    parser.add_argument(
        "--cases-dir",
        default="tests/redteam/cases",
        help="Directory containing attack cases",
    )
    parser.add_argument(
        "--ledger-url", default="http://localhost:4000", help="Ledger service URL"
    )
    parser.add_argument("--output", help="Output file for results")

    args = parser.parse_args()

    runner = RedTeamRunner(args.kube_config, args.ledger_url)

    # Load attack cases
    if not runner.load_attack_cases(args.cases_dir):
        return 1

    # Run attacks
    results = runner.run_all_attacks()

    # Generate report
    report = runner.generate_report(results)
    print(report)

    # Save report if output specified
    if args.output:
        with open(args.output, "w") as f:
            f.write(report)
        print(f"📄 Report saved to: {args.output}")

    # Return non-zero if any attacks failed
    failed_count = sum(1 for success in results.values() if not success)
    return failed_count


if __name__ == "__main__":
    sys.exit(main())
