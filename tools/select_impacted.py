#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Impacted Target Selector.
Reads changed files from git diff and returns affected Lean targets via reverse-deps lookup.
"""

import argparse
import json
import os
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
    lean_files = filter_lean_files(changed_files)
    if not lean_files:
        return set()

    dep_graph = LeanDepGraph(workspace_root)
    dep_graph.build_dependency_graph()

    # Get impacted modules
    impacted_modules = dep_graph.get_impacted_modules(lean_files)

    # Convert to build targets
    build_targets = dep_graph.get_build_targets(impacted_modules)

    return set(build_targets)


def get_impacted_tests(workspace_root: str, changed_files: List[str]) -> Set[str]:
    """Get impacted test file paths from changed files (pytest-compatible)."""
    impacted_tests: Set[str] = set()
    test_file_patterns = (
        r"tests/.*\.py$",
        r"tests/.*\.js$",
        r"tests/perf/.*\.js$",
        r"tests/.*\.go$",
        r"tests/.*\.rs$",
        r"bench/.*\.py$",
    )

    for file_path in changed_files:
        if any(re.match(pattern, file_path) for pattern in test_file_patterns):
            impacted_tests.add(file_path)
            continue

        # Lean proof changes map to nearest pytest gate when present
        if re.match(r"bundles/.*/proofs/.*\.lean$", file_path) or re.match(
            r"core/.*\.lean$", file_path
        ):
            lean_gate = Path(workspace_root) / "tools" / "ci" / "test_impacted_only.py"
            if lean_gate.is_file():
                impacted_tests.add(str(lean_gate.relative_to(workspace_root)).replace("\\", "/"))

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


def build_result(
    workspace_root: str, changed_files: List[str]
) -> dict:
    """Compute impacted targets/tests/agents for changed files."""
    impacted_targets = get_impacted_targets(workspace_root, changed_files)
    impacted_tests = get_impacted_tests(workspace_root, changed_files)
    impacted_agents = get_impacted_agents(workspace_root, changed_files)
    allowlist_impacted = get_impacted_allowlist(workspace_root, changed_files)
    return {
        "changed_files": changed_files,
        "impacted_targets": sorted(impacted_targets),
        "impacted_tests": sorted(impacted_tests),
        "impacted_agents": sorted(impacted_agents),
        "allowlist_impacted": allowlist_impacted,
        "allowlist_needs_update": allowlist_impacted,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Select Lean bundles, tests, and agents impacted by git changes."
    )
    parser.add_argument(
        "workspace_root",
        nargs="?",
        default=".",
        help="Repository root (positional; prefer --root in CI)",
    )
    parser.add_argument(
        "base_ref",
        nargs="?",
        default=None,
        help="Git ref to diff against (positional; prefer --base-ref in CI)",
    )
    parser.add_argument("--root", dest="root", default=None, help="Repository root")
    parser.add_argument(
        "--base-ref",
        dest="base_ref_flag",
        default=None,
        help="Git ref to diff against (default: main or GITHUB_EVENT_BEFORE)",
    )
    parser.add_argument(
        "--output",
        "-o",
        default=None,
        help="Write JSON results to this path (used by reusable-ci-prepare)",
    )
    return parser.parse_args()


def resolve_base_ref(args: argparse.Namespace) -> str:
    if args.base_ref_flag:
        return args.base_ref_flag
    if args.base_ref:
        return args.base_ref
    return os.environ.get("GITHUB_EVENT_BEFORE") or "main"


def main():
    """Main entry point."""
    args = parse_args()
    workspace_root = args.root or args.workspace_root
    base_ref = resolve_base_ref(args)

    # Get changed files
    changed_files = get_changed_files(workspace_root, base_ref)

    if not changed_files:
        print("No changed files found")
        if args.output:
            result = build_result(workspace_root, [])
            output_path = Path(args.output)
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
            print(f"Wrote empty JSON output to {output_path}")
        sys.exit(0)

    print(f"Changed files: {len(changed_files)}")
    for file_path in changed_files:
        print(f"  - {file_path}")

    result = build_result(workspace_root, changed_files)
    impacted_targets = result["impacted_targets"]
    impacted_tests = result["impacted_tests"]
    impacted_agents = result["impacted_agents"]
    allowlist_impacted = result["allowlist_impacted"]

    # Print summary
    print(f"\nImpacted targets: {len(impacted_targets)}")
    for target in impacted_targets:
        print(f"  - {target}")

    print(f"\nImpacted tests: {len(impacted_tests)}")
    for test in impacted_tests:
        print(f"  - {test}")

    print(f"\nImpacted agents: {len(impacted_agents)}")
    for agent in impacted_agents:
        print(f"  - {agent}")

    print(f"\nAllowlist impacted: {allowlist_impacted}")

    # Output for CI consumption
    print("\n--- TARGETS ---")
    for target in impacted_targets:
        print(target)

    print("\n--- TESTS ---")
    for test in impacted_tests:
        print(test)

    print("\n--- AGENTS ---")
    for agent in impacted_agents:
        print(agent)

    if args.output:
        output_path = Path(args.output)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"\nWrote JSON output to {output_path}")
    else:
        print(f"\nJSON output:\n{json.dumps(result, indent=2)}")


if __name__ == "__main__":
    main()
