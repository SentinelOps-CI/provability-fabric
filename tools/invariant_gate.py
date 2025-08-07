#!/usr/bin/env python3
"""
Invariant Gate - ensures all bundles import and use required invariants
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Set


class InvariantGate:
    def __init__(self):
        self.required_invariants = {
            "non_interference_invariant",
            "capability_soundness_invariant",
            "pii_egress_protection_invariant",
            "plan_separation_invariant",
        }

        self.required_imports = {"Invariants"}

    def scan_bundle_directory(self, bundle_dir: str) -> Dict[str, List[str]]:
        """Scan bundle directory for Lean files and check invariant usage"""
        results = {"missing_imports": [], "missing_invariants": [], "valid_bundles": []}

        bundle_path = Path(bundle_dir)
        if not bundle_path.exists():
            print(f"Bundle directory {bundle_dir} does not exist")
            return results

        # Find all bundle directories
        for bundle in bundle_path.iterdir():
            if bundle.is_dir() and bundle.name not in [".lake", "__pycache__"]:
                bundle_results = self.check_bundle_invariants(bundle)

                if bundle_results["missing_imports"]:
                    results["missing_imports"].append(
                        {
                            "bundle": bundle.name,
                            "files": bundle_results["missing_imports"],
                        }
                    )

                if bundle_results["missing_invariants"]:
                    results["missing_invariants"].append(
                        {
                            "bundle": bundle.name,
                            "files": bundle_results["missing_invariants"],
                        }
                    )

                if (
                    not bundle_results["missing_imports"]
                    and not bundle_results["missing_invariants"]
                ):
                    results["valid_bundles"].append(bundle.name)

        return results

    def check_bundle_invariants(self, bundle_path: Path) -> Dict[str, List[str]]:
        """Check a single bundle for invariant usage"""
        results = {"missing_imports": [], "missing_invariants": []}

        # Look for Lean files in the bundle
        lean_files = list(bundle_path.rglob("*.lean"))

        for lean_file in lean_files:
            file_results = self.check_lean_file_invariants(lean_file)

            if file_results["missing_imports"]:
                results["missing_imports"].append(str(lean_file))

            if file_results["missing_invariants"]:
                results["missing_invariants"].append(str(lean_file))

        return results

    def check_lean_file_invariants(self, lean_file: Path) -> Dict[str, List[str]]:
        """Check a single Lean file for invariant usage"""
        results = {"missing_imports": [], "missing_invariants": []}

        try:
            with open(lean_file, "r", encoding="utf-8") as f:
                content = f.read()

            # Check for required imports
            if not self.has_required_imports(content):
                results["missing_imports"].append("Invariants")

            # Check for invariant usage
            missing_invariants = self.get_missing_invariants(content)
            if missing_invariants:
                results["missing_invariants"].extend(missing_invariants)

        except Exception as e:
            print(f"Error reading {lean_file}: {e}")
            results["missing_imports"].append("Error reading file")

        return results

    def has_required_imports(self, content: str) -> bool:
        """Check if file imports required modules"""
        # Look for import statements
        import_pattern = r"import\s+(\w+)"
        imports = re.findall(import_pattern, content)

        return "Invariants" in imports

    def get_missing_invariants(self, content: str) -> List[str]:
        """Find missing invariant usage in the file"""
        missing = []

        # Look for invariant usage patterns
        for invariant in self.required_invariants:
            # Check for theorem statements that use the invariant
            theorem_pattern = rf"theorem.*{invariant}"
            if not re.search(theorem_pattern, content, re.IGNORECASE):
                # Check for direct usage in proofs
                usage_pattern = rf"{invariant}"
                if not re.search(usage_pattern, content):
                    missing.append(invariant)

        return missing

    def generate_invariant_template(self, bundle_name: str) -> str:
        """Generate a template for invariant usage"""
        template = f"""
-- Invariant usage template for {bundle_name}
import Invariants

-- Example theorem using invariants
theorem {bundle_name}_invariant_safety (trace : ActionTrace) (caps : List Capability) 
         (kernel_approvals : List String) (epsilon_max : Float) :
  non_interference_invariant trace ∧
  capability_soundness_invariant trace caps ∧
  pii_egress_protection_invariant trace ∧
  plan_separation_invariant trace kernel_approvals := by
  -- Proof that this bundle satisfies all invariants
  sorry

-- Example usage of specific invariants
theorem {bundle_name}_non_interference (trace : ActionTrace) :
  non_interference_invariant trace := by
  sorry

theorem {bundle_name}_capability_soundness (trace : ActionTrace) (caps : List Capability) :
  capability_soundness_invariant trace caps := by
  sorry

theorem {bundle_name}_pii_protection (trace : ActionTrace) :
  pii_egress_protection_invariant trace := by
  sorry

theorem {bundle_name}_plan_separation (trace : ActionTrace) (kernel_approvals : List String) :
  plan_separation_invariant trace kernel_approvals := by
  sorry
"""
        return template

    def run_gate_check(self, bundle_dir: str) -> bool:
        """Run the invariant gate check"""
        print("Running invariant gate check...")

        results = self.scan_bundle_directory(bundle_dir)

        # Report results
        if results["valid_bundles"]:
            print(f"✓ Valid bundles: {', '.join(results['valid_bundles'])}")

        if results["missing_imports"]:
            print("✗ Bundles missing required imports:")
            for bundle in results["missing_imports"]:
                print(f"  - {bundle['bundle']}: {', '.join(bundle['files'])}")

        if results["missing_invariants"]:
            print("✗ Bundles missing invariant usage:")
            for bundle in results["missing_invariants"]:
                print(f"  - {bundle['bundle']}: {', '.join(bundle['files'])}")

        # Generate templates for missing bundles
        if results["missing_imports"] or results["missing_invariants"]:
            print("\nGenerating templates for missing invariants...")
            for bundle in results["missing_imports"] + results["missing_invariants"]:
                bundle_name = bundle["bundle"]
                template = self.generate_invariant_template(bundle_name)

                template_file = (
                    Path(bundle_dir) / bundle_name / "proofs" / "Invariants.lean"
                )
                template_file.parent.mkdir(parents=True, exist_ok=True)

                with open(template_file, "w") as f:
                    f.write(template)

                print(f"  - Generated template: {template_file}")

        # Return success if no issues
        return (
            len(results["missing_imports"]) == 0
            and len(results["missing_invariants"]) == 0
        )


def main():
    """Main function"""
    if len(sys.argv) != 2:
        print("Usage: python invariant_gate.py <bundle_directory>")
        sys.exit(1)

    bundle_dir = sys.argv[1]
    gate = InvariantGate()

    success = gate.run_gate_check(bundle_dir)

    if success:
        print("\n✓ All bundles pass invariant gate check")
        sys.exit(0)
    else:
        print("\n✗ Some bundles failed invariant gate check")
        sys.exit(1)


if __name__ == "__main__":
    main()
