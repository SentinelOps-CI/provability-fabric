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

    if not impacted_targets:
        print("\nNo impacted Lean targets found")
        sys.exit(0)

    print(f"\nImpacted targets: {len(impacted_targets)}")
    for target in sorted(impacted_targets):
        print(f"  - {target}")

    # Output for CI consumption (one target per line)
    print("\n--- TARGETS ---")
    for target in sorted(impacted_targets):
        print(target)

    # Output JSON for further processing
    result = {
        "changed_files": changed_files,
        "impacted_targets": list(impacted_targets),
    }
    print(f"\nJSON output:\n{json.dumps(result, indent=2)}")


if __name__ == "__main__":
    main()
