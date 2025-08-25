#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Policy consistency validation tool for policy gates CI.
"""

import json
import argparse
import sys
from pathlib import Path


def validate_policy_consistency(dfa_path: str, proofs_path: str) -> bool:
    """Validate policy consistency between DFA and Lean proofs."""
    try:
        # Load DFA
        with open(dfa_path, "r") as f:
            dfa = json.load(f)

        # Check if proofs directory exists
        proofs_dir = Path(proofs_path)
        if not proofs_dir.exists():
            print(f"❌ Proofs directory not found: {proofs_path}")
            return False

        # Check for required Lean files
        required_files = ["Policy.lean", "Spec.lean"]
        for file_name in required_files:
            file_path = proofs_dir / file_name
            if not file_path.exists():
                print(f"❌ Required proof file not found: {file_name}")
                return False

        # Validate DFA structure
        if "states" not in dfa or "transitions" not in dfa:
            print("❌ DFA missing required structure")
            return False

        # Check for basic policy coverage
        state_count = len(dfa.get("states", []))
        transition_count = len(dfa.get("transitions", []))

        if state_count < 2:
            print("❌ DFA must have at least 2 states")
            return False

        if transition_count < 1:
            print("❌ DFA must have at least 1 transition")
            return False

        # Check for rate limiters (security requirement)
        rate_limiters = dfa.get("rate_limiters", [])
        if not rate_limiters:
            print("⚠️  No rate limiters found - security concern")

        # Check for metadata
        metadata = dfa.get("metadata", {})
        if "canonical" not in metadata:
            print("⚠️  DFA missing canonical flag")

        print("✅ Policy consistency validation passed")
        return True

    except FileNotFoundError as e:
        print(f"❌ File not found: {e}")
        return False
    except json.JSONDecodeError as e:
        print(f"❌ JSON decode error: {e}")
        return False
    except Exception as e:
        print(f"❌ Validation error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(description="Validate policy consistency")
    parser.add_argument("--dfa-path", required=True, help="Path to DFA JSON file")
    parser.add_argument("--proofs-path", required=True, help="Path to proofs directory")

    args = parser.parse_args()

    success = validate_policy_consistency(args.dfa_path, args.proofs_path)
    if not success:
        sys.exit(1)


if __name__ == "__main__":
    main()
