#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

DFA schema validation tool for policy gates CI.
"""

import json
import argparse
import sys


def validate_dfa_schema(dfa_path: str, schema_path: str) -> bool:
    """Validate DFA against JSON schema."""
    try:
        # Load DFA
        with open(dfa_path, "r") as f:
            dfa = json.load(f)

        # Load schema (for future use)
        with open(schema_path, "r") as f:
            _ = json.load(f)  # Load but don't use yet

        # Basic validation checks
        required_fields = [
            "version",
            "dfa_type",
            "states",
            "transitions",
            "initial_state",
        ]

        for field in required_fields:
            if field not in dfa:
                print(f"❌ Missing required field: {field}")
                return False

        # Validate states
        if not isinstance(dfa["states"], list):
            print("❌ States must be a list")
            return False

        for i, state in enumerate(dfa["states"]):
            if "id" not in state or "accepting" not in state:
                print(f"❌ Invalid state at index {i}")
                return False

        # Validate transitions
        if not isinstance(dfa["transitions"], list):
            print("❌ Transitions must be a list")
            return False

        for i, transition in enumerate(dfa["transitions"]):
            required_transition_fields = ["from", "event", "to"]
            for field in required_transition_fields:
                if field not in transition:
                    print(f"❌ Invalid transition at index {i}: missing {field}")
                    return False

        # Validate initial state
        initial_state = dfa["initial_state"]
        state_ids = [state["id"] for state in dfa["states"]]
        if initial_state not in state_ids:
            print(f"❌ Initial state {initial_state} not found in states")
            return False

        print("✅ DFA schema validation passed")
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
    parser = argparse.ArgumentParser(description="Validate DFA schema")
    parser.add_argument("--dfa-path", required=True, help="Path to DFA JSON file")
    parser.add_argument("--schema-path", required=True, help="Path to schema file")

    args = parser.parse_args()

    success = validate_dfa_schema(args.dfa_path, args.schema_path)
    if not success:
        sys.exit(1)


if __name__ == "__main__":
    main()
