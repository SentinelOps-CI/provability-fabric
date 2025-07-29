#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Stochastic Proof-Regression Harness
Performs random spec perturbations to test proof robustness and detect regressions.
"""

import os
import sys
import json
import random
import subprocess
import tempfile
import argparse
import time
from pathlib import Path
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass
from datetime import datetime
import yaml
import git
from concurrent.futures import ThreadPoolExecutor, as_completed


@dataclass
class PerturbationResult:
    """Result of a perturbation test"""

    perturbation_type: str
    perturbation_params: Dict[str, Any]
    original_spec: str
    perturbed_spec: str
    proof_status: str  # "PASS", "FAIL", "TIMEOUT", "ERROR"
    proof_output: str
    execution_time: float
    regression_detected: bool
    error_message: Optional[str] = None


@dataclass
class RegressionTest:
    """Configuration for a regression test"""

    name: str
    spec_file: str
    proof_file: str
    perturbation_types: List[str]
    num_iterations: int
    timeout_seconds: int
    expected_behavior: str  # "STABLE", "FAIL_SAFE", "FAIL_FAST"


class StochasticHarness:
    """Stochastic proof-regression testing harness"""

    def __init__(self, config_path: str = "config.yaml"):
        self.config = self._load_config(config_path)
        self.results: List[PerturbationResult] = []
        self.repo = git.Repo(".")
        self.random_seed = self.config.get("random_seed", 42)
        random.seed(self.random_seed)

    def _load_config(self, config_path: str) -> Dict[str, Any]:
        """Load configuration from YAML file"""
        if not os.path.exists(config_path):
            return self._get_default_config()

        with open(config_path, "r") as f:
            return yaml.safe_load(f)

    def _get_default_config(self) -> Dict[str, Any]:
        """Get default configuration"""
        return {
            "perturbation_types": [
                "parameter_noise",
                "constraint_relaxation",
                "constraint_tightening",
                "requirement_addition",
                "requirement_removal",
                "metric_adjustment",
                "timeout_adjustment",
                "resource_limit_adjustment",
            ],
            "parameter_noise_range": 0.05,  # ±5%
            "constraint_adjustment_range": 0.10,  # ±10%
            "metric_adjustment_range": 0.15,  # ±15%
            "num_trials": 50,
            "min_success_rate": 0.95,  # 95%
            "parallel_workers": 4,
            "spec_templates_path": "spec-templates",
            "lean_libs_path": "core/lean-libs",
            "output_path": "results",
            "log_level": "INFO",
            "save_intermediate_results": True,
            "random_seed": 42,
        }

    def find_spec_files(self) -> List[str]:
        """Find all specification files in the project"""
        spec_files = []
        spec_path = self.config.get("spec_templates_path", "spec-templates")

        for pattern in ["**/spec.yaml", "**/spec.yml", "**/*.spec.yaml"]:
            spec_files.extend(Path(spec_path).glob(pattern))
        return [str(f) for f in spec_files]

    def find_proof_files(self) -> List[str]:
        """Find all proof files in the project"""
        proof_files = []
        lean_path = self.config.get("lean_libs_path", "core/lean-libs")

        for pattern in ["**/*.lean", "**/proofs/**/*.lean"]:
            proof_files.extend(Path(lean_path).glob(pattern))
        return [str(f) for f in proof_files]

    def load_spec(self, spec_path: str) -> Dict[str, Any]:
        """Load a specification file"""
        with open(spec_path, "r") as f:
            return yaml.safe_load(f)

    def save_spec(self, spec: Dict[str, Any], path: str):
        """Save a specification to file"""
        with open(path, "w") as f:
            yaml.dump(spec, f, default_flow_style=False)

    def apply_parameter_noise(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Apply random noise to numeric parameters (±5%)"""
        perturbed_spec = spec.copy()
        noise_range = self.config.get("parameter_noise_range", 0.05)

        def add_noise_to_value(value, noise_range):
            if isinstance(value, (int, float)):
                noise = random.uniform(-noise_range, noise_range)
                return value * (1 + noise)
            return value

        def perturb_dict(d, noise_range):
            for key, value in d.items():
                if isinstance(value, dict):
                    perturb_dict(value, noise_range)
                elif isinstance(value, list):
                    for i, item in enumerate(value):
                        if isinstance(item, dict):
                            perturb_dict(item, noise_range)
                        else:
                            value[i] = add_noise_to_value(item, noise_range)
                else:
                    d[key] = add_noise_to_value(value, noise_range)

        perturb_dict(perturbed_spec, noise_range)
        return perturbed_spec

    def apply_constraint_relaxation(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Relax constraints in the specification"""
        perturbed_spec = spec.copy()
        adjustment_range = self.config.get("constraint_adjustment_range", 0.10)

        def relax_constraints(d):
            for key, value in d.items():
                if isinstance(value, dict):
                    relax_constraints(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            relax_constraints(item)
                elif key in ["limit", "threshold", "max", "min", "timeout"]:
                    if isinstance(value, (int, float)):
                        if "max" in key or "limit" in key:
                            d[key] = value * (1 + adjustment_range)
                        elif "min" in key:
                            d[key] = value * (1 - adjustment_range)
                        elif "timeout" in key:
                            d[key] = value * (1 + adjustment_range)

        relax_constraints(perturbed_spec)
        return perturbed_spec

    def apply_constraint_tightening(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Tighten constraints in the specification"""
        perturbed_spec = spec.copy()
        adjustment_range = self.config.get("constraint_adjustment_range", 0.10)

        def tighten_constraints(d):
            for key, value in d.items():
                if isinstance(value, dict):
                    tighten_constraints(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            tighten_constraints(item)
                elif key in ["limit", "threshold", "max", "min", "timeout"]:
                    if isinstance(value, (int, float)):
                        if "max" in key or "limit" in key:
                            d[key] = value * (1 - adjustment_range)
                        elif "min" in key:
                            d[key] = value * (1 + adjustment_range)
                        elif "timeout" in key:
                            d[key] = value * (1 - adjustment_range)

        tighten_constraints(perturbed_spec)
        return perturbed_spec

    def apply_requirement_addition(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Add new requirements to the specification"""
        perturbed_spec = spec.copy()

        # Add a new requirement
        if "requirements" not in perturbed_spec:
            perturbed_spec["requirements"] = {}

        new_req_id = f"REQ-{random.randint(1000, 9999)}"
        perturbed_spec["requirements"][new_req_id] = {
            "statement": f"Additional requirement for robustness testing",
            "rationale": "Added by stochastic harness",
            "metric": "100% compliance",
            "owner": "Test Harness",
            "priority": random.choice(["low", "medium", "high"]),
            "category": "robustness",
        }

        return perturbed_spec

    def apply_requirement_removal(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Remove random requirements from the specification"""
        perturbed_spec = spec.copy()

        if "requirements" in perturbed_spec and perturbed_spec["requirements"]:
            req_ids = list(perturbed_spec["requirements"].keys())
            if req_ids:
                # Remove a random requirement (but not critical ones)
                removable_reqs = [
                    req_id for req_id in req_ids if not req_id.startswith("REQ-000")
                ]  # Don't remove core requirements
                if removable_reqs:
                    req_to_remove = random.choice(removable_reqs)
                    del perturbed_spec["requirements"][req_to_remove]

        return perturbed_spec

    def apply_metric_adjustment(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Adjust metric thresholds in the specification"""
        perturbed_spec = spec.copy()
        adjustment_range = self.config.get("metric_adjustment_range", 0.15)

        def adjust_metrics(d):
            for key, value in d.items():
                if isinstance(value, dict):
                    adjust_metrics(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            adjust_metrics(item)
                elif key in ["metric", "threshold", "target"]:
                    if isinstance(value, str) and any(
                        op in value for op in ["≤", "≥", "<", ">", "="]
                    ):
                        # Parse and adjust numeric thresholds in metric strings
                        import re

                        numbers = re.findall(r"\d+\.?\d*", value)
                        if numbers:
                            for num_str in numbers:
                                num = float(num_str)
                                adjustment = random.uniform(
                                    -adjustment_range, adjustment_range
                                )
                                new_num = num * (1 + adjustment)
                                value = value.replace(num_str, f"{new_num:.2f}")
                            d[key] = value

        adjust_metrics(perturbed_spec)
        return perturbed_spec

    def apply_timeout_adjustment(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Adjust timeout values in the specification"""
        perturbed_spec = spec.copy()

        def adjust_timeouts(d):
            for key, value in d.items():
                if isinstance(value, dict):
                    adjust_timeouts(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            adjust_timeouts(item)
                elif "timeout" in key.lower():
                    if isinstance(value, (int, float)):
                        adjustment = random.uniform(0.5, 2.0)
                        d[key] = value * adjustment

        adjust_timeouts(perturbed_spec)
        return perturbed_spec

    def apply_resource_limit_adjustment(
        self, spec: Dict[str, Any], params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Adjust resource limits in the specification"""
        perturbed_spec = spec.copy()

        def adjust_resource_limits(d):
            for key, value in d.items():
                if isinstance(value, dict):
                    adjust_resource_limits(value)
                elif isinstance(value, list):
                    for item in value:
                        if isinstance(item, dict):
                            adjust_resource_limits(item)
                elif any(
                    term in key.lower()
                    for term in ["memory", "cpu", "storage", "network"]
                ):
                    if isinstance(value, (int, float)):
                        adjustment = random.uniform(0.7, 1.5)
                        d[key] = value * adjustment

        adjust_resource_limits(perturbed_spec)
        return perturbed_spec

    def run_proof_check(
        self, spec_path: str, proof_path: str, timeout_seconds: int
    ) -> Tuple[str, str, float]:
        """Run proof checking on a specification"""
        start_time = time.time()

        try:
            # Run Lean proof checking
            cmd = ["lake", "build", "--", spec_path]
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                cwd=os.path.dirname(proof_path) if proof_path else ".",
            )

            execution_time = time.time() - start_time

            if result.returncode == 0:
                return "PASS", result.stdout, execution_time
            else:
                return "FAIL", result.stderr, execution_time

        except subprocess.TimeoutExpired:
            execution_time = time.time() - start_time
            return "TIMEOUT", "Proof checking timed out", execution_time
        except Exception as e:
            execution_time = time.time() - start_time
            return "ERROR", str(e), execution_time

    def apply_perturbation(
        self, spec: Dict[str, Any], perturbation_type: str, params: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Apply a specific perturbation to the specification"""
        perturbation_methods = {
            "parameter_noise": self.apply_parameter_noise,
            "constraint_relaxation": self.apply_constraint_relaxation,
            "constraint_tightening": self.apply_constraint_tightening,
            "requirement_addition": self.apply_requirement_addition,
            "requirement_removal": self.apply_requirement_removal,
            "metric_adjustment": self.apply_metric_adjustment,
            "timeout_adjustment": self.apply_timeout_adjustment,
            "resource_limit_adjustment": self.apply_resource_limit_adjustment,
        }

        if perturbation_type in perturbation_methods:
            return perturbation_methods[perturbation_type](spec, params)
        else:
            raise ValueError(f"Unknown perturbation type: {perturbation_type}")

    def run_single_test(
        self, test_config: RegressionTest, iteration: int
    ) -> PerturbationResult:
        """Run a single perturbation test"""
        # Load original specification
        original_spec = self.load_spec(test_config.spec_file)

        # Choose random perturbation type
        perturbation_type = random.choice(test_config.perturbation_types)

        # Apply perturbation
        perturbed_spec = self.apply_perturbation(
            original_spec, perturbation_type, self.config
        )

        # Save perturbed spec to temporary file
        with tempfile.NamedTemporaryFile(mode="w", suffix=".yaml", delete=False) as f:
            yaml.dump(perturbed_spec, f)
            perturbed_spec_path = f.name

        try:
            # Run proof check
            proof_status, proof_output, execution_time = self.run_proof_check(
                perturbed_spec_path, test_config.proof_file, test_config.timeout_seconds
            )

            # Determine if regression was detected
            regression_detected = False
            if test_config.expected_behavior == "STABLE":
                regression_detected = proof_status != "PASS"
            elif test_config.expected_behavior == "FAIL_SAFE":
                regression_detected = proof_status == "ERROR"
            elif test_config.expected_behavior == "FAIL_FAST":
                regression_detected = proof_status == "TIMEOUT"

            return PerturbationResult(
                perturbation_type=perturbation_type,
                perturbation_params=self.config.get("perturbation_settings", {}).get(
                    perturbation_type, {}
                ),
                original_spec=yaml.dump(original_spec),
                perturbed_spec=yaml.dump(perturbed_spec),
                proof_status=proof_status,
                proof_output=proof_output,
                execution_time=execution_time,
                regression_detected=regression_detected,
            )

        finally:
            # Clean up temporary file
            os.unlink(perturbed_spec_path)

    def run_regression_tests(
        self, tests: List[RegressionTest]
    ) -> List[PerturbationResult]:
        """Run all regression tests"""
        all_results = []

        for test in tests:
            print(f"Running regression test: {test.name}")
            print(f"  Spec file: {test.spec_file}")
            print(f"  Proof file: {test.proof_file}")
            print(f"  Iterations: {test.num_iterations}")

            # Run tests in parallel
            with ThreadPoolExecutor(
                max_workers=self.config.get("parallel_workers", 4)
            ) as executor:
                futures = [
                    executor.submit(self.run_single_test, test, i)
                    for i in range(test.num_iterations)
                ]

                for future in as_completed(futures):
                    try:
                        result = future.result()
                        all_results.append(result)

                        if result.regression_detected:
                            print(
                                f"  ⚠️  Regression detected: {result.perturbation_type}"
                            )
                        else:
                            print(f"  ✓ Test passed: {result.perturbation_type}")

                    except Exception as e:
                        print(f"  ✗ Test failed: {e}")

        return all_results

    def generate_summary_report(
        self, results: List[PerturbationResult], output_dir: str
    ):
        """Generate a summary report for CI"""
        total_trials = len(results)
        passed_trials = len([r for r in results if not r.regression_detected])
        failed_trials = len([r for r in results if r.regression_detected])
        success_rate = passed_trials / total_trials if total_trials > 0 else 0

        # Group results by perturbation type
        perturbation_results = {}
        for result in results:
            if result.perturbation_type not in perturbation_results:
                perturbation_results[result.perturbation_type] = {
                    "passed": 0,
                    "total": 0,
                }

            perturbation_results[result.perturbation_type]["total"] += 1
            if not result.regression_detected:
                perturbation_results[result.perturbation_type]["passed"] += 1

        # Calculate success rates for each perturbation type
        for pert_type, stats in perturbation_results.items():
            stats["success_rate"] = (
                stats["passed"] / stats["total"] if stats["total"] > 0 else 0
            )

        summary = {
            "total_trials": total_trials,
            "passed_trials": passed_trials,
            "failed_trials": failed_trials,
            "success_rate": success_rate,
            "random_seed": self.random_seed,
            "perturbation_results": perturbation_results,
            "timestamp": datetime.now().isoformat(),
            "config": {
                "parameter_noise_range": self.config.get("parameter_noise_range", 0.05),
                "constraint_adjustment_range": self.config.get(
                    "constraint_adjustment_range", 0.10
                ),
                "metric_adjustment_range": self.config.get(
                    "metric_adjustment_range", 0.15
                ),
                "min_success_rate": self.config.get("min_success_rate", 0.95),
            },
        }

        # Ensure output directory exists
        os.makedirs(output_dir, exist_ok=True)

        # Save summary report
        summary_path = os.path.join(output_dir, "summary.json")
        with open(summary_path, "w") as f:
            json.dump(summary, f, indent=2)

        print(f"\nSummary Report:")
        print(f"  Total trials: {total_trials}")
        print(f"  Passed: {passed_trials}")
        print(f"  Failed: {failed_trials}")
        print(
            f"  Success rate: {success_rate:.3f} (minimum: {self.config.get('min_success_rate', 0.95):.3f})"
        )
        print(f"  Random seed: {self.random_seed}")

        for pert_type, stats in perturbation_results.items():
            print(
                f"  {pert_type}: {stats['passed']}/{stats['total']} ({stats['success_rate']:.3f})"
            )

        return summary

    def generate_detailed_report(
        self, results: List[PerturbationResult], output_dir: str
    ):
        """Generate a detailed test report"""
        report = {
            "summary": {
                "total_tests": len(results),
                "passed": len([r for r in results if not r.regression_detected]),
                "regressions": len([r for r in results if r.regression_detected]),
                "timeout": len([r for r in results if r.proof_status == "TIMEOUT"]),
                "errors": len([r for r in results if r.proof_status == "ERROR"]),
            },
            "perturbation_stats": {},
            "regressions": [],
            "detailed_results": [],
        }

        # Calculate perturbation statistics
        for result in results:
            if result.perturbation_type not in report["perturbation_stats"]:
                report["perturbation_stats"][result.perturbation_type] = {
                    "total": 0,
                    "passed": 0,
                    "regressions": 0,
                }

            stats = report["perturbation_stats"][result.perturbation_type]
            stats["total"] += 1
            if result.regression_detected:
                stats["regressions"] += 1
                report["regressions"].append(
                    {
                        "perturbation_type": result.perturbation_type,
                        "proof_status": result.proof_status,
                        "execution_time": result.execution_time,
                        "error_message": result.error_message,
                    }
                )
            else:
                stats["passed"] += 1

        # Add detailed results
        for result in results:
            report["detailed_results"].append(
                {
                    "perturbation_type": result.perturbation_type,
                    "proof_status": result.proof_status,
                    "execution_time": result.execution_time,
                    "regression_detected": result.regression_detected,
                    "error_message": result.error_message,
                }
            )

        # Save detailed report
        detailed_path = os.path.join(output_dir, "detailed_report.json")
        with open(detailed_path, "w") as f:
            json.dump(report, f, indent=2)

        print(f"\nDetailed report saved to: {detailed_path}")
        print(
            f"Summary: {report['summary']['passed']}/{report['summary']['total_tests']} tests passed"
        )
        if report["summary"]["regressions"] > 0:
            print(f"⚠️  {report['summary']['regressions']} regressions detected!")


def main():
    parser = argparse.ArgumentParser(description="Stochastic Proof-Regression Harness")
    parser.add_argument("--config", default="config.yaml", help="Configuration file")
    parser.add_argument("--trials", type=int, default=50, help="Number of trials")
    parser.add_argument("--output", default="results", help="Output directory")
    parser.add_argument("--spec-file", help="Specific spec file to test")
    parser.add_argument(
        "--random-seed", type=int, help="Random seed for reproducibility"
    )
    parser.add_argument("--timeout", type=int, default=300, help="Timeout in seconds")

    args = parser.parse_args()

    # Initialize harness
    harness = StochasticHarness(args.config)

    # Override random seed if provided
    if args.random_seed:
        harness.random_seed = args.random_seed
        random.seed(args.random_seed)

    # Find test configurations
    if args.spec_file:
        spec_files = [args.spec_file]
    else:
        spec_files = harness.find_spec_files()

    proof_files = harness.find_proof_files()

    if not spec_files:
        print("No specification files found!")
        sys.exit(1)

    # Create test configurations
    tests = []
    for spec_file in spec_files:
        # Find corresponding proof file
        proof_file = None
        for proof in proof_files:
            if os.path.dirname(spec_file) in proof:
                proof_file = proof
                break

        test = RegressionTest(
            name=f"stochastic_test_{len(tests)}",
            spec_file=spec_file,
            proof_file=proof_file or "",
            perturbation_types=harness.config["perturbation_types"],
            num_iterations=args.trials,
            timeout_seconds=args.timeout,
            expected_behavior="STABLE",
        )
        tests.append(test)

    print(f"Found {len(tests)} test configurations")
    print(f"Running {args.trials} trials per test")
    print(f"Random seed: {harness.random_seed}")

    # Run tests
    results = harness.run_regression_tests(tests)

    # Generate reports
    harness.generate_summary_report(results, args.output)
    harness.generate_detailed_report(results, args.output)

    # Check success rate against minimum threshold
    total_trials = len(results)
    passed_trials = len([r for r in results if not r.regression_detected])
    success_rate = passed_trials / total_trials if total_trials > 0 else 0
    min_success_rate = harness.config.get("min_success_rate", 0.95)

    print(f"\nFinal Results:")
    print(f"  Success rate: {success_rate:.3f} (minimum: {min_success_rate:.3f})")

    if success_rate < min_success_rate:
        print(f"❌ Success rate below minimum threshold! CI should fail.")
        sys.exit(1)
    else:
        print(f"✅ Success rate meets minimum threshold.")


if __name__ == "__main__":
    main()
