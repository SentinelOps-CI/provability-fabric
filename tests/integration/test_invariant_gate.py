#!/usr/bin/env python3
"""
Test invariant gate - verifies that the gate correctly identifies missing invariants
"""

import os
import tempfile
import shutil
from pathlib import Path
from tools.invariant_gate import InvariantGate


class InvariantGateTest:
    def __init__(self):
        self.gate = InvariantGate()

    def create_test_bundle(
        self, bundle_name: str, has_imports: bool = True, has_invariants: bool = True
    ) -> Path:
        """Create a test bundle with specified characteristics"""
        temp_dir = Path(tempfile.mkdtemp())
        bundle_dir = temp_dir / bundle_name
        proofs_dir = bundle_dir / "proofs"
        proofs_dir.mkdir(parents=True)

        # Create Spec.lean file
        spec_content = self.generate_spec_content(has_imports, has_invariants)
        spec_file = proofs_dir / "Spec.lean"
        spec_file.write_text(spec_content)

        return temp_dir

    def generate_spec_content(self, has_imports: bool, has_invariants: bool) -> str:
        """Generate Spec.lean content based on test parameters"""
        content = """
-- Test bundle spec
"""

        if has_imports:
            content += """
import Invariants
"""

        content += """
namespace Spec

-- Basic theorem
theorem basic_theorem : True := by
  trivial
"""

        if has_invariants:
            content += """

-- Invariant usage
theorem test_invariant_safety (trace : ActionTrace) (caps : List Capability) 
         (kernel_approvals : List String) (epsilon_max : Float) :
  non_interference_invariant trace ∧
  capability_soundness_invariant trace caps ∧
  pii_egress_protection_invariant trace ∧
  plan_separation_invariant trace kernel_approvals := by
  sorry

theorem test_non_interference (trace : ActionTrace) :
  non_interference_invariant trace := by
  sorry
"""

        content += """
end Spec
"""
        return content

    def test_valid_bundle(self):
        """Test that a valid bundle passes the gate"""
        print("Testing valid bundle...")

        temp_dir = self.create_test_bundle(
            "valid-bundle", has_imports=True, has_invariants=True
        )

        try:
            results = self.gate.scan_bundle_directory(str(temp_dir))

            assert (
                "valid-bundle" in results["valid_bundles"]
            ), f"Valid bundle should be in valid_bundles, got: {results}"
            assert (
                len(results["missing_imports"]) == 0
            ), f"No missing imports expected, got: {results['missing_imports']}"
            assert (
                len(results["missing_invariants"]) == 0
            ), f"No missing invariants expected, got: {results['missing_invariants']}"

            print("✓ Valid bundle test passed")

        finally:
            shutil.rmtree(temp_dir)

    def test_missing_imports(self):
        """Test that bundles without imports are detected"""
        print("Testing missing imports...")

        temp_dir = self.create_test_bundle(
            "missing-imports", has_imports=False, has_invariants=True
        )

        try:
            results = self.gate.scan_bundle_directory(str(temp_dir))

            assert (
                len(results["missing_imports"]) > 0
            ), f"Should detect missing imports, got: {results}"
            assert any(
                "missing-imports" in bundle["bundle"]
                for bundle in results["missing_imports"]
            ), f"Should find missing-imports bundle, got: {results}"

            print("✓ Missing imports test passed")

        finally:
            shutil.rmtree(temp_dir)

    def test_missing_invariants(self):
        """Test that bundles without invariant usage are detected"""
        print("Testing missing invariants...")

        temp_dir = self.create_test_bundle(
            "missing-invariants", has_imports=True, has_invariants=False
        )

        try:
            results = self.gate.scan_bundle_directory(str(temp_dir))

            assert (
                len(results["missing_invariants"]) > 0
            ), f"Should detect missing invariants, got: {results}"
            assert any(
                "missing-invariants" in bundle["bundle"]
                for bundle in results["missing_invariants"]
            ), f"Should find missing-invariants bundle, got: {results}"

            print("✓ Missing invariants test passed")

        finally:
            shutil.rmtree(temp_dir)

    def test_mixed_bundles(self):
        """Test multiple bundles with different characteristics"""
        print("Testing mixed bundles...")

        temp_dir = Path(tempfile.mkdtemp())

        try:
            # Create multiple test bundles
            self.create_test_bundle_in_dir(
                temp_dir, "valid-bundle", has_imports=True, has_invariants=True
            )
            self.create_test_bundle_in_dir(
                temp_dir, "missing-imports", has_imports=False, has_invariants=True
            )
            self.create_test_bundle_in_dir(
                temp_dir, "missing-invariants", has_imports=True, has_invariants=False
            )
            self.create_test_bundle_in_dir(
                temp_dir, "missing-both", has_imports=False, has_invariants=False
            )

            results = self.gate.scan_bundle_directory(str(temp_dir))

            # Check results
            assert (
                "valid-bundle" in results["valid_bundles"]
            ), "Valid bundle should be valid"
            assert (
                len(results["missing_imports"]) == 2
            ), f"Should find 2 bundles missing imports, got: {len(results['missing_imports'])}"
            assert (
                len(results["missing_invariants"]) == 2
            ), f"Should find 2 bundles missing invariants, got: {len(results['missing_invariants'])}"

            print("✓ Mixed bundles test passed")

        finally:
            shutil.rmtree(temp_dir)

    def create_test_bundle_in_dir(
        self,
        parent_dir: Path,
        bundle_name: str,
        has_imports: bool,
        has_invariants: bool,
    ):
        """Create a test bundle in the specified directory"""
        bundle_dir = parent_dir / bundle_name
        proofs_dir = bundle_dir / "proofs"
        proofs_dir.mkdir(parents=True)

        spec_content = self.generate_spec_content(has_imports, has_invariants)
        spec_file = proofs_dir / "Spec.lean"
        spec_file.write_text(spec_content)

    def test_template_generation(self):
        """Test that templates are generated for missing invariants"""
        print("Testing template generation...")

        temp_dir = self.create_test_bundle(
            "needs-template", has_imports=False, has_invariants=False
        )

        try:
            # Run gate check which should generate templates
            success = self.gate.run_gate_check(str(temp_dir))

            # Check that template was generated
            template_file = temp_dir / "needs-template" / "proofs" / "Invariants.lean"
            assert not success, "Gate check should fail for missing invariants"
            assert (
                template_file.exists()
            ), f"Template file should be generated at {template_file}"

            # Check template content
            content = template_file.read_text()
            assert "import Invariants" in content, "Template should import Invariants"
            assert (
                "non_interference_invariant" in content
            ), "Template should include invariant usage"

            print("✓ Template generation test passed")

        finally:
            shutil.rmtree(temp_dir)

    def run_all_tests(self):
        """Run all invariant gate tests"""
        print("Running invariant gate tests...")

        self.test_valid_bundle()
        self.test_missing_imports()
        self.test_missing_invariants()
        self.test_mixed_bundles()
        self.test_template_generation()

        print("All invariant gate tests passed! ✓")


def main():
    """Main test runner"""
    test = InvariantGateTest()
    test.run_all_tests()


if __name__ == "__main__":
    main()
