#!/usr/bin/env python3
"""Simple test script to verify capability check functionality."""

import json
import sys
from pathlib import Path


def test_capability_check():
    """Test the capability check functionality."""
    print("🧪 Testing capability check functionality...")

    # Check if files exist
    lean_file = Path("core/lean-libs/Capability.lean")
    json_file = Path("runtime/sidecar-watcher/policy/allowlist.json")

    print(f"Lean file exists: {lean_file.exists()}")
    print(f"JSON file exists: {json_file.exists()}")

    if not lean_file.exists():
        print("❌ Lean file not found")
        return False

    if not json_file.exists():
        print("❌ JSON file not found")
        return False

    # Read and parse JSON
    try:
        with open(json_file) as f:
            config = json.load(f)

        print("✅ JSON file parsed successfully")
        print(f"Agents in JSON: {list(config.get('agents', {}).keys())}")

        # Check for test-agent-2
        if "test-agent-2" in config.get("agents", {}):
            agent_config = config["agents"]["test-agent-2"]
            allowed_tools = agent_config.get("allowed_tools", [])
            print(f"test-agent-2 allowed tools: {allowed_tools}")

            expected_tools = {"SendEmail", "LogSpend", "LogAction"}
            actual_tools = set(allowed_tools)

            if actual_tools == expected_tools:
                print("✅ test-agent-2 tools match expected")
                return True
            else:
                print(f"❌ test-agent-2 tools mismatch:")
                print(f"  Expected: {expected_tools}")
                print(f"  Actual: {actual_tools}")
                return False
        else:
            print("❌ test-agent-2 not found in JSON")
            return False

    except Exception as e:
        print(f"❌ Error parsing JSON: {e}")
        return False


if __name__ == "__main__":
    success = test_capability_check()
    sys.exit(0 if success else 1)
