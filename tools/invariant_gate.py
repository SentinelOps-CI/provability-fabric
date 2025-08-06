#!/usr/bin/env python3
"""
Invariant Gate - CI tool to ensure system invariants are properly referenced and proven.

This tool checks that:
1. All bundle specs import and use system invariants
2. No 'sorry' proofs remain in invariant theorems
3. All required invariants are covered
4. Proofs compile successfully
"""

import os
import sys
import re
import subprocess
import argparse
from pathlib import Path
from typing import List, Tuple, Dict, Set
import yaml


class InvariantGate:
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.core_libs = self.project_root / "core" / "lean-libs"
        self.bundles_dir = self.project_root / "bundles"

        # Required invariants that must be used
        self.required_invariants = {
            "non_interference": "Tenant isolation - no cross-tenant data flow",
            "capability_soundness": "All actions require valid capabilities",
            "plan_separation": "No action without kernel approval",
            "pii_egress_protection": "No PII data in outputs",
            "dp_bound": "Differential privacy budget limits",
        }

        # Files that should import Invariants
        self.invariant_users = set()

        self.errors = []
        self.warnings = []

    def check_all(self) -> bool:
        """Run all invariant checks."""
        print("🔍 Running Invariant Gate checks...")

        success = True

        # Check 1: Invariants.lean compilation
        if not self.check_invariants_compilation():
            success = False

        # Check 2: Bundle invariant usage
        if not self.check_bundle_invariant_usage():
            success = False

        # Check 3: No sorry proofs in invariants
        if not self.check_no_sorry_proofs():
            success = False

        # Check 4: Coverage of required invariants
        if not self.check_invariant_coverage():
            success = False

        # Check 5: Lean proof verification
        if not self.verify_lean_proofs():
            success = False

        self.print_summary()
        return success

    def check_invariants_compilation(self) -> bool:
        """Check that Invariants.lean compiles successfully."""
        print("📋 Checking Invariants.lean compilation...")

        invariants_file = self.core_libs / "Invariants.lean"
        if not invariants_file.exists():
            self.errors.append(f"Invariants.lean not found at {invariants_file}")
            return False

        try:
            result = subprocess.run(
                ["lean", "--check", str(invariants_file)],
                capture_output=True,
                text=True,
                cwd=self.project_root,
            )

            if result.returncode != 0:
                self.errors.append(
                    f"Invariants.lean compilation failed:\n{result.stderr}"
                )
                return False

            print("✅ Invariants.lean compiles successfully")
            return True

        except FileNotFoundError:
            self.errors.append("Lean compiler not found. Please install Lean 4.")
            return False

    def check_bundle_invariant_usage(self) -> bool:
        """Check that all bundles import and use invariants."""
        print("📦 Checking bundle invariant usage...")

        success = True

        for bundle_dir in self.bundles_dir.iterdir():
            if not bundle_dir.is_dir():
                continue

            spec_file = bundle_dir / "proofs" / "Spec.lean"
            if not spec_file.exists():
                self.warnings.append(f"No Spec.lean found in bundle {bundle_dir.name}")
                continue

            if not self.check_bundle_spec(spec_file, bundle_dir.name):
                success = False

        return success

    def check_bundle_spec(self, spec_file: Path, bundle_name: str) -> bool:
        """Check a specific bundle spec for invariant usage."""
        try:
            content = spec_file.read_text()
        except Exception as e:
            self.errors.append(f"Could not read {spec_file}: {e}")
            return False

        # Check for Invariants import
        if not re.search(r"import.*Invariants", content):
            self.errors.append(
                f"Bundle {bundle_name}: Missing 'import Invariants' in Spec.lean"
            )
            return False

        # Check for at least one invariant usage
        invariant_usage = False
        for invariant in self.required_invariants:
            if invariant in content:
                invariant_usage = True
                self.invariant_users.add(bundle_name)
                break

        if not invariant_usage:
            self.errors.append(
                f"Bundle {bundle_name}: No system invariants used in Spec.lean"
            )
            return False

        print(f"✅ Bundle {bundle_name}: Proper invariant usage")
        return True

    def check_no_sorry_proofs(self) -> bool:
        """Check that no 'sorry' proofs remain in critical invariant theorems."""
        print("🚫 Checking for sorry proofs in invariants...")

        invariants_file = self.core_libs / "Invariants.lean"
        if not invariants_file.exists():
            return False

        try:
            content = invariants_file.read_text()
        except Exception as e:
            self.errors.append(f"Could not read Invariants.lean: {e}")
            return False

        # Find critical theorem definitions
        critical_theorems = [
            "empty_trace_invariant",
            "invariant_preservation",
            "cross_tenant_isolation",
            "system_safety",
        ]

        sorry_found = False
        for theorem in critical_theorems:
            # Look for theorem definition and check for sorry in its proof
            theorem_pattern = rf"theorem\s+{theorem}.*?:=\s*by\s*(.*?)(?=theorem|\Z)"
            match = re.search(theorem_pattern, content, re.DOTALL | re.MULTILINE)

            if match:
                proof_body = match.group(1)
                if "sorry" in proof_body:
                    self.errors.append(f"Theorem {theorem} contains 'sorry' proof")
                    sorry_found = True

        if sorry_found:
            return False

        print("✅ No sorry proofs found in critical invariant theorems")
        return True

    def check_invariant_coverage(self) -> bool:
        """Check that all required invariants are covered by at least one bundle."""
        print("📊 Checking invariant coverage...")

        # Scan all bundle specs for invariant usage
        used_invariants = set()

        for bundle_dir in self.bundles_dir.iterdir():
            if not bundle_dir.is_dir():
                continue

            spec_file = bundle_dir / "proofs" / "Spec.lean"
            if not spec_file.exists():
                continue

            try:
                content = spec_file.read_text()
                for invariant in self.required_invariants:
                    if invariant in content:
                        used_invariants.add(invariant)
            except Exception:
                continue

        # Check coverage
        missing_invariants = set(self.required_invariants.keys()) - used_invariants

        if missing_invariants:
            for invariant in missing_invariants:
                description = self.required_invariants[invariant]
                self.errors.append(
                    f"Invariant '{invariant}' not used by any bundle - {description}"
                )
            return False

        print(f"✅ All {len(self.required_invariants)} required invariants are covered")
        return True

    def verify_lean_proofs(self) -> bool:
        """Verify that all Lean proofs compile successfully."""
        print("🔬 Verifying Lean proofs...")

        # Find all .lean files in bundles
        lean_files = []
        for bundle_dir in self.bundles_dir.iterdir():
            if bundle_dir.is_dir():
                proofs_dir = bundle_dir / "proofs"
                if proofs_dir.exists():
                    lean_files.extend(proofs_dir.glob("*.lean"))

        if not lean_files:
            self.warnings.append("No Lean proof files found")
            return True

        failed_files = []
        for lean_file in lean_files:
            try:
                result = subprocess.run(
                    ["lean", "--check", str(lean_file)],
                    capture_output=True,
                    text=True,
                    cwd=self.project_root,
                )

                if result.returncode != 0:
                    failed_files.append((lean_file, result.stderr))

            except FileNotFoundError:
                self.errors.append("Lean compiler not found")
                return False

        if failed_files:
            for lean_file, error in failed_files:
                self.errors.append(
                    f"Proof verification failed for {lean_file}:\n{error}"
                )
            return False

        print(f"✅ All {len(lean_files)} proof files verified successfully")
        return True

    def print_summary(self):
        """Print summary of check results."""
        print("\n" + "=" * 60)
        print("INVARIANT GATE SUMMARY")
        print("=" * 60)

        if self.errors:
            print(f"❌ {len(self.errors)} ERROR(S):")
            for i, error in enumerate(self.errors, 1):
                print(f"  {i}. {error}")

        if self.warnings:
            print(f"⚠️  {len(self.warnings)} WARNING(S):")
            for i, warning in enumerate(self.warnings, 1):
                print(f"  {i}. {warning}")

        if not self.errors and not self.warnings:
            print("✅ ALL CHECKS PASSED - System invariants properly enforced!")
        elif not self.errors:
            print("✅ CHECKS PASSED with warnings")
        else:
            print("❌ CHECKS FAILED - Fix errors before proceeding")

        # Statistics
        print(f"\n📈 STATISTICS:")
        print(f"  - Required invariants: {len(self.required_invariants)}")
        print(f"  - Bundles using invariants: {len(self.invariant_users)}")
        print(f"  - Core invariant theorems verified")


def main():
    parser = argparse.ArgumentParser(
        description="Invariant Gate - CI tool for system invariants"
    )
    parser.add_argument("--project-root", default=".", help="Project root directory")
    parser.add_argument(
        "--fail-on-warnings", action="store_true", help="Fail on warnings"
    )

    args = parser.parse_args()

    gate = InvariantGate(args.project_root)
    success = gate.check_all()

    # Fail on warnings if requested
    if args.fail_on_warnings and gate.warnings:
        success = False

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
