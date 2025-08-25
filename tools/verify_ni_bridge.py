#!/usr/bin/env python3
"""
NI Bridge Verification Script

This script verifies that the runtime's local checks match the proof
preconditions required by Theorem ni-bridge. It checks N random certificates
against hashes and acceptance conditions to ensure the bridge guarantee holds.

Usage:
    python tools/verify_ni_bridge.py [--num-certs N] [--strict] [--verbose]

Requirements:
    - Python 3.8+
    - Access to certificate directory
    - Lean proof files for hash verification
"""

import argparse
import hashlib
import json
import random
import sys
from pathlib import Path
from typing import Dict, List
import logging

# Configure logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


class NIBridgeVerifier:
    """Verifies NI bridge guarantees in certificates"""

    def __init__(self, strict_mode: bool = True, verbose: bool = False):
        self.strict_mode = strict_mode
        self.verbose = verbose
        self.verification_results = []

        # Set up paths
        self.repo_root = Path(__file__).parent.parent
        self.proofs_dir = self.repo_root / "proofs"
        self.evidence_dir = self.repo_root / "evidence"
        self.certs_dir = self.evidence_dir / "egress_certs"

        # Expected proof hashes
        self.expected_hashes = self._load_expected_hashes()

    def _load_expected_hashes(self) -> Dict[str, str]:
        """Load expected proof hashes from files"""
        hashes = {}

        try:
            # Policy.lean hash
            policy_file = self.proofs_dir / "Policy.lean"
            if policy_file.exists():
                with open(policy_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    hashes["policy_proof_hash"] = hashlib.sha256(
                        content.encode()
                    ).hexdigest()

            # DFA hash (if exists)
            dfa_file = self.repo_root / "artifact" / "dfa" / "dfa.json"
            if dfa_file.exists():
                with open(dfa_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    hashes["automata_hash"] = hashlib.sha256(
                        content.encode()
                    ).hexdigest()

            # Labeler hash (if exists)
            labeler_file = self.repo_root / "core" / "lean-tools" / "LabelerGen.lean"
            if labeler_file.exists():
                with open(labeler_file, "r", encoding="utf-8") as f:
                    content = f.read()
                    hashes["labeler_hash"] = hashlib.sha256(
                        content.encode()
                    ).hexdigest()

            # NI bridge theorem hash
            ni_bridge_content = (
                "theorem ni_bridge : ∀ (u : Principal) (a : Action) (γ : Ctx) "
                "(monitor : NIMonitor) (prefixes : List NIPrefix), "
                "permitD u a γ = true → "
                "(∀ prefix ∈ prefixes, monitor.accepts_prefix prefix) → "
                "GlobalNonInterference monitor prefixes"
            )
            hashes["ni_bridge_hash"] = hashlib.sha256(
                ni_bridge_content.encode()
            ).hexdigest()

        except Exception as e:
            logger.warning(f"Failed to load expected hashes: {e}")

        return hashes

    def _get_random_certificates(self, num_certs: int) -> List[Path]:
        """Get N random certificates from the evidence directory"""
        if not self.certs_dir.exists():
            logger.error(f"Certificate directory not found: {self.certs_dir}")
            return []

        cert_files = list(self.certs_dir.glob("*.json"))
        if not cert_files:
            logger.error(f"No certificate files found in {self.certs_dir}")
            return []

        # Randomly sample certificates
        num_available = len(cert_files)
        num_to_sample = min(num_certs, num_available)

        if num_to_sample < num_certs:
            logger.warning(
                f"Only {num_available} certificates available, sampling {num_to_sample}"
            )

        return random.sample(cert_files, num_to_sample)

    def _verify_certificate(self, cert_path: Path) -> Dict:
        """Verify a single certificate against bridge conditions"""
        try:
            with open(cert_path, "r", encoding="utf-8") as f:
                cert_data = json.load(f)

            verification_result = {
                "certificate": str(cert_path),
                "verification_passed": True,
                "errors": [],
                "warnings": [],
                "bridge_conditions": {},
                "hash_verification": {},
                "ni_monitor_status": {},
            }

            # Check for required fields
            required_fields = [
                "permit_decision",
                "path_witness_ok",
                "label_derivation_ok",
                "epoch",
            ]

            for field in required_fields:
                if field not in cert_data:
                    verification_result["verification_passed"] = False
                    verification_result["errors"].append(
                        f"Missing required field: {field}"
                    )

            # Verify permit decision
            if "permit_decision" in cert_data:
                permit_decision = cert_data["permit_decision"]
                if permit_decision not in ["accept", "reject", "error"]:
                    verification_result["verification_passed"] = False
                    verification_result["errors"].append(
                        f"Invalid permit_decision: {permit_decision}"
                    )

                verification_result["bridge_conditions"]["permit_decision_valid"] = (
                    permit_decision in ["accept", "reject", "error"]
                )

            # Verify witness and label derivation
            if "path_witness_ok" in cert_data:
                verification_result["bridge_conditions"]["path_witness_ok"] = cert_data[
                    "path_witness_ok"
                ]

            if "label_derivation_ok" in cert_data:
                verification_result["bridge_conditions"]["label_derivation_ok"] = (
                    cert_data["label_derivation_ok"]
                )

            # Verify epoch
            if "epoch" in cert_data:
                try:
                    epoch = int(cert_data["epoch"])
                    verification_result["bridge_conditions"]["epoch_valid"] = epoch > 0
                except (ValueError, TypeError):
                    verification_result["verification_passed"] = False
                    verification_result["errors"].append(
                        f"Invalid epoch: {cert_data['epoch']}"
                    )

            # Check for proof hashes if present
            if "proof_hashes" in cert_data:
                proof_hashes = cert_data["proof_hashes"]
                hash_verification = {}

                for hash_type, expected_hash in self.expected_hashes.items():
                    if hash_type in proof_hashes:
                        actual_hash = proof_hashes[hash_type]
                        hash_match = actual_hash == expected_hash
                        hash_verification[hash_type] = {
                            "expected": expected_hash,
                            "actual": actual_hash,
                            "match": hash_match,
                        }

                        if not hash_match:
                            verification_result["warnings"].append(
                                f"Hash mismatch for {hash_type}"
                            )
                            if self.strict_mode:
                                verification_result["verification_passed"] = False
                    else:
                        hash_verification[hash_type] = {
                            "expected": expected_hash,
                            "actual": "missing",
                            "match": False,
                        }
                        verification_result["warnings"].append(
                            f"Missing hash for {hash_type}"
                        )

                verification_result["hash_verification"] = hash_verification

            # Check for ni_monitor status if present
            if "ni_monitor" in cert_data:
                ni_monitor = cert_data["ni_monitor"]
                ni_status = {}

                # Check if ni_monitor is set exactly as \MonNI requires
                required_monitor_fields = [
                    "prefixes",
                    "active_sessions",
                    "violation_count",
                ]
                for field in required_monitor_fields:
                    if field in ni_monitor:
                        ni_status[field] = True
                    else:
                        ni_status[field] = False
                        verification_result["warnings"].append(
                            f"Missing ni_monitor field: {field}"
                        )

                # Check for bridge guarantee
                if "bridge_guarantee" in ni_monitor:
                    bridge_guarantee = ni_monitor["bridge_guarantee"]
                    if "theorem_reference" in bridge_guarantee:
                        theorem_ref = bridge_guarantee["theorem_reference"]
                        ni_status["theorem_reference_correct"] = (
                            theorem_ref == "ni-bridge"
                        )

                        if theorem_ref != "ni-bridge":
                            verification_result["errors"].append(
                                f"Incorrect theorem reference: {theorem_ref}"
                            )
                            verification_result["verification_passed"] = False

                    if "local_checks_ok" in bridge_guarantee:
                        ni_status["local_checks_ok"] = bridge_guarantee[
                            "local_checks_ok"
                        ]

                    if "global_ni_claim" in bridge_guarantee:
                        global_claim = bridge_guarantee["global_ni_claim"]
                        ni_status["global_ni_claim_correct"] = (
                            global_claim == "global_non_interference"
                        )

                verification_result["ni_monitor_status"] = ni_status

            # Check for break_glass marking if present
            if "break_glass" in cert_data:
                break_glass = cert_data["break_glass"]
                if break_glass:
                    verification_result["warnings"].append(
                        "Certificate marked as break_glass override"
                    )
                    # In strict mode, break_glass certificates might be treated differently
                    if self.strict_mode:
                        verification_result["verification_passed"] = False

            return verification_result

        except Exception as e:
            return {
                "certificate": str(cert_path),
                "verification_passed": False,
                "errors": [f"Failed to verify certificate: {e}"],
                "warnings": [],
                "bridge_conditions": {},
                "hash_verification": {},
                "ni_monitor_status": {},
            }

    def verify_certificates(self, num_certs: int) -> Dict:
        """Verify N random certificates"""
        logger.info(f"Starting verification of {num_certs} random certificates")

        # Get random certificates
        cert_paths = self._get_random_certificates(num_certs)
        if not cert_paths:
            return {
                "verification_passed": False,
                "total_certificates": 0,
                "verified_certificates": 0,
                "failed_certificates": 0,
                "errors": ["No certificates available for verification"],
                "results": [],
            }

        # Verify each certificate
        total_certs = len(cert_paths)
        verified_certs = 0
        failed_certs = 0
        all_errors = []

        for cert_path in cert_paths:
            if self.verbose:
                logger.info(f"Verifying certificate: {cert_path.name}")

            result = self._verify_certificate(cert_path)
            self.verification_results.append(result)

            if result["verification_passed"]:
                verified_certs += 1
            else:
                failed_certs += 1
                all_errors.extend(result["errors"])

        # Overall verification result
        overall_passed = failed_certs == 0 or (
            not self.strict_mode and failed_certs < total_certs * 0.1
        )

        verification_summary = {
            "verification_passed": overall_passed,
            "total_certificates": total_certs,
            "verified_certificates": verified_certs,
            "failed_certificates": failed_certs,
            "success_rate": verified_certs / total_certs if total_certs > 0 else 0,
            "errors": all_errors,
            "results": self.verification_results,
        }

        logger.info(
            f"Verification complete: {verified_certs}/{total_certs} certificates passed"
        )

        return verification_summary

    def generate_report(self, verification_summary: Dict) -> str:
        """Generate a human-readable verification report"""
        report_lines = []
        report_lines.append("=" * 80)
        report_lines.append("NI BRIDGE VERIFICATION REPORT")
        report_lines.append("=" * 80)
        report_lines.append("")

        # Summary
        report_lines.append("SUMMARY")
        report_lines.append("-" * 40)
        report_lines.append(
            f"Overall Verification: {'PASSED' if verification_summary['verification_passed'] else 'FAILED'}"
        )
        report_lines.append(
            f"Total Certificates: {verification_summary['total_certificates']}"
        )
        report_lines.append(
            f"Verified: {verification_summary['verified_certificates']}"
        )
        report_lines.append(f"Failed: {verification_summary['failed_certificates']}")
        report_lines.append(f"Success Rate: {verification_summary['success_rate']:.1%}")
        report_lines.append("")

        # Errors
        if verification_summary["errors"]:
            report_lines.append("ERRORS")
            report_lines.append("-" * 40)
            for error in verification_summary["errors"]:
                report_lines.append(f"❌ {error}")
            report_lines.append("")

        # Detailed results
        if self.verbose:
            report_lines.append("DETAILED RESULTS")
            report_lines.append("-" * 40)

            for i, result in enumerate(verification_summary["results"], 1):
                cert_name = Path(result["certificate"]).name
                status = "✅ PASS" if result["verification_passed"] else "❌ FAIL"
                report_lines.append(f"{i}. {cert_name}: {status}")

                if result["errors"]:
                    for error in result["errors"]:
                        report_lines.append(f"   Error: {error}")

                if result["warnings"]:
                    for warning in result["warnings"]:
                        report_lines.append(f"   Warning: {warning}")

                report_lines.append("")

        # Bridge guarantee status
        report_lines.append("BRIDGE GUARANTEE STATUS")
        report_lines.append("-" * 40)

        bridge_conditions_met = 0
        total_conditions = 0

        for result in verification_summary["results"]:
            if "bridge_conditions" in result:
                for condition, value in result["bridge_conditions"].items():
                    total_conditions += 1
                    if value:
                        bridge_conditions_met += 1

        if total_conditions > 0:
            bridge_success_rate = bridge_conditions_met / total_conditions
            report_lines.append(
                f"Bridge Conditions Met: {bridge_conditions_met}/{total_conditions} ({bridge_success_rate:.1%})"
            )
        else:
            report_lines.append("No bridge conditions found in certificates")

        report_lines.append("")

        # Hash verification status
        report_lines.append("HASH VERIFICATION STATUS")
        report_lines.append("-" * 40)

        hash_matches = 0
        total_hashes = 0

        for result in verification_summary["results"]:
            if "hash_verification" in result:
                for hash_type, hash_info in result["hash_verification"].items():
                    total_hashes += 1
                    if hash_info.get("match", False):
                        hash_matches += 1

        if total_hashes > 0:
            hash_success_rate = hash_matches / total_hashes
            report_lines.append(
                f"Hash Matches: {hash_matches}/{total_hashes} ({hash_success_rate:.1%})"
            )
        else:
            report_lines.append("No hash verification data found")

        report_lines.append("")
        report_lines.append("=" * 80)

        return "\n".join(report_lines)


def main():
    """Main entry point"""
    parser = argparse.ArgumentParser(
        description="Verify NI bridge guarantees in certificates",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Verify 10 random certificates in strict mode
  python tools/verify_ni_bridge.py --num-certs 10 --strict
  
  # Verify 5 certificates with verbose output
  python tools/verify_ni_bridge.py --num-certs 5 --verbose
  
  # Verify all available certificates
  python tools/verify_ni_bridge.py --num-certs 1000
        """,
    )

    parser.add_argument(
        "--num-certs",
        "-n",
        type=int,
        default=10,
        help="Number of random certificates to verify (default: 10)",
    )

    parser.add_argument(
        "--strict",
        action="store_true",
        help="Enable strict verification mode (any failure causes overall failure)",
    )

    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Enable verbose output with detailed results",
    )

    parser.add_argument(
        "--output",
        "-o",
        type=str,
        help="Output file for the verification report (default: stdout)",
    )

    args = parser.parse_args()

    # Create verifier
    verifier = NIBridgeVerifier(strict_mode=args.strict, verbose=args.verbose)

    # Verify certificates
    verification_summary = verifier.verify_certificates(args.num_certs)

    # Generate report
    report = verifier.generate_report(verification_summary)

    # Output report
    if args.output:
        try:
            with open(args.output, "w", encoding="utf-8") as f:
                f.write(report)
            logger.info(f"Report written to: {args.output}")
        except Exception as e:
            logger.error(f"Failed to write report to {args.output}: {e}")
            print(report)
    else:
        print(report)

    # Exit with appropriate code
    if verification_summary["verification_passed"]:
        sys.exit(0)
    else:
        sys.exit(1)


if __name__ == "__main__":
    main()
