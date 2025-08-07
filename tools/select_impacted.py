#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Impacted Target Selector.
Reads changed files from git diff and returns affected Lean targets via reverse-deps lookup.
"""

import json
import subprocess
import sys
import re
from pathlib import Path
from typing import List, Set
from lean_dep_graph import LeanDepGraph


def get_changed_files(workspace_root: str, base_ref: str = "main") -> List[str]:
    """Get list of changed files from git diff."""
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", base_ref],
            capture_output=True,
            text=True,
            cwd=workspace_root,
        )

        if result.returncode == 0:
            return [line.strip() for line in result.stdout.splitlines() if line.strip()]
        else:
            print(f"Warning: Could not get git diff: {result.stderr}")
            return []

    except Exception as e:
        print(f"Warning: Error getting git diff: {e}")
        return []


def filter_lean_files(changed_files: List[str]) -> List[str]:
    """Filter to only Lean files."""
    lean_files = []

    for file_path in changed_files:
        if file_path.endswith(".lean"):
            lean_files.append(file_path)

    return lean_files


def get_impacted_targets(workspace_root: str, changed_files: List[str]) -> Set[str]:
    """Get impacted build targets from changed files."""
    dep_graph = LeanDepGraph(workspace_root)
    dep_graph.build_dependency_graph()

    # Filter to Lean files
    lean_files = filter_lean_files(changed_files)

    if not lean_files:
        return set()

    # Get impacted modules
    impacted_modules = dep_graph.get_impacted_modules(lean_files)

    # Convert to build targets
    build_targets = dep_graph.get_build_targets(impacted_modules)

    return set(build_targets)


def get_impacted_tests(workspace_root: str, changed_files: List[str]) -> Set[str]:
    """Get impacted tests from changed files."""
    impacted_tests = set()

    # Map file patterns to test types
    test_patterns = {
        r"tests/.*\.py$": "python_test",
        r"tests/.*\.js$": "javascript_test",
        r"tests/.*\.go$": "go_test",
        r"tests/.*\.rs$": "rust_test",
        r"bundles/.*/proofs/.*\.lean$": "lean_proof",
        r"core/.*\.lean$": "lean_spec",
    }

    for file_path in changed_files:
        for pattern, test_type in test_patterns.items():
            if re.match(pattern, file_path):
                # Extract test name from path
                test_name = Path(file_path).stem
                impacted_tests.add(f"{test_type}:{test_name}")
                break

    return impacted_tests


def get_impacted_allowlist(workspace_root: str, changed_files: List[str]) -> bool:
    """Check if allowlist needs to be regenerated."""
    allowlist_triggers = [
        "core/lean-libs/",
        "bundles/",
        "tools/gen_allowlist_from_lean.py",
        "runtime/sidecar-watcher/policy/allowlist.json",
    ]

    for file_path in changed_files:
        for trigger in allowlist_triggers:
            if trigger in file_path:
                return True

    return False


def get_impacted_agents(workspace_root: str, changed_files: List[str]) -> Set[str]:
    """Get impacted agents from changed files."""
    impacted_agents = set()

    # Look for bundle changes
    for file_path in changed_files:
        if "bundles/" in file_path:
            # Extract agent name from bundle path
            parts = file_path.split("/")
            if len(parts) >= 3 and parts[0] == "bundles":
                agent_name = parts[1]
                impacted_agents.add(agent_name)

    return impacted_agents


def main():
    """Main entry point."""
    if len(sys.argv) < 2:
        print("Usage: python3 tools/select_impacted.py <workspace_root> [base_ref]")
        sys.exit(1)

    workspace_root = sys.argv[1]
    base_ref = sys.argv[2] if len(sys.argv) > 2 else "main"

    # Get changed files
    changed_files = get_changed_files(workspace_root, base_ref)

    if not changed_files:
        print("No changed files found")
        sys.exit(0)

    print(f"Changed files: {len(changed_files)}")
    for file_path in changed_files:
        print(f"  - {file_path}")

    # Get impacted targets
    impacted_targets = get_impacted_targets(workspace_root, changed_files)
    impacted_tests = get_impacted_tests(workspace_root, changed_files)
    impacted_agents = get_impacted_agents(workspace_root, changed_files)
    allowlist_impacted = get_impacted_allowlist(workspace_root, changed_files)

    # Print summary
    print(f"\nImpacted targets: {len(impacted_targets)}")
    for target in sorted(impacted_targets):
        print(f"  - {target}")

    print(f"\nImpacted tests: {len(impacted_tests)}")
    for test in sorted(impacted_tests):
        print(f"  - {test}")

    print(f"\nImpacted agents: {len(impacted_agents)}")
    for agent in sorted(impacted_agents):
        print(f"  - {agent}")

    print(f"\nAllowlist impacted: {allowlist_impacted}")

    # Output for CI consumption
    print("\n--- TARGETS ---")
    for target in sorted(impacted_targets):
        print(target)

    print("\n--- TESTS ---")
    for test in sorted(impacted_tests):
        print(test)

    print("\n--- AGENTS ---")
    for agent in sorted(impacted_agents):
        print(agent)

    # Output JSON for further processing
    result = {
        "changed_files": changed_files,
        "impacted_targets": list(impacted_targets),
        "impacted_tests": list(impacted_tests),
        "impacted_agents": list(impacted_agents),
        "allowlist_impacted": allowlist_impacted,
    }
    print(f"\nJSON output:\n{json.dumps(result, indent=2)}")


if __name__ == "__main__":
    main()
