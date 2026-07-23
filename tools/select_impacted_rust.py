#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Map changed paths to Cargo workspace package names for path-aware Rust CI.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Iterable, List, Set

# Path prefix -> cargo package name (must match Cargo.toml package names).
PATH_TO_CRATE: list[tuple[str, str]] = [
    ("runtime/sidecar-watcher/", "sidecar-watcher"),
    ("runtime/retrieval-gateway/", "retrieval-gateway"),
    ("runtime/telemetry-service/", "telemetry-service"),
    ("runtime/jwks-manager/", "jwks-manager"),
    ("runtime/mpc-fintech/", "mpc-fintech"),
    ("runtime/egress-firewall/", "egress-firewall"),
    ("runtime/tool-broker/", "tool-broker"),
    ("runtime/attestor/", "attestor"),
    ("runtime/kms-proxy/", "kms-proxy"),
    ("runtime/labeler/", "labeler"),
    ("runtime/wasm-sandbox/", "wasm-sandbox"),
    ("core/crypto/dsse-rs/", "dsse-rs"),
    ("core/sdk/rust/", "provability-fabric-core-sdk-rust"),
    ("adapters/http-get/", "http-get"),
    ("adapters/file-read/", "file-read"),
    ("bench/", "provability-fabric-bench"),
]

# Crates with curated CI targets (not full cargo test -p).
CURATED_CRATES = {
    "sidecar-watcher",
    "retrieval-gateway",
    "telemetry-service",
    "jwks-manager",
    "mpc-fintech",
    "egress-firewall",
}

# Excluded from default workspace-libs cargo test (curated or special).
WORKSPACE_EXCLUDE = CURATED_CRATES | {
    "provability-fabric-core-sdk-rust",
    "labeler",
    "tool-broker",
}


def get_changed_files(root: Path, base_ref: str) -> List[str]:
    cmds = [
        ["git", "diff", "--name-only", f"{base_ref}...HEAD"],
        ["git", "diff", "--name-only", base_ref],
        ["git", "diff", "--name-only", "HEAD~1"],
    ]
    for cmd in cmds:
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, cwd=root, check=False
            )
            if result.returncode == 0 and result.stdout.strip():
                return [ln.strip() for ln in result.stdout.splitlines() if ln.strip()]
        except OSError:
            continue
    return []


def crates_from_files(files: Iterable[str]) -> Set[str]:
    crates: Set[str] = set()
    for path in files:
        norm = path.replace("\\", "/")
        if norm in ("Cargo.toml", "Cargo.lock"):
            continue
        for prefix, crate in PATH_TO_CRATE:
            if norm.startswith(prefix) or norm == prefix.rstrip("/"):
                crates.add(crate)
                break
    return crates


def forces_full(files: Iterable[str]) -> bool:
    for path in files:
        norm = path.replace("\\", "/")
        if norm in ("Cargo.toml", "Cargo.lock"):
            return True
        if norm.startswith(".github/workflows/reusable-ci-rust"):
            return True
        if norm.startswith(".github/actions/cache-cargo"):
            return True
    return False


def build_result(files: List[str], full_workspace: bool) -> dict:
    if full_workspace or forces_full(files):
        return {
            "full_workspace": True,
            "changed_files": files,
            "impacted_crates": [],
            "curated_crates": sorted(CURATED_CRATES),
            "workspace_crates": [],
            "run_sidecar_curated": True,
            "run_workspace_libs": True,
        }

    crates = crates_from_files(files)
    curated = sorted(crates & CURATED_CRATES)
    workspace = sorted(c for c in crates if c not in WORKSPACE_EXCLUDE)
    # If only scripts/gates changed under rust slice with no crate map, run curated floor.
    if not crates:
        return {
            "full_workspace": False,
            "changed_files": files,
            "impacted_crates": [],
            "curated_crates": sorted(CURATED_CRATES),
            "workspace_crates": [],
            "run_sidecar_curated": True,
            "run_workspace_libs": True,
        }

    return {
        "full_workspace": False,
        "changed_files": files,
        "impacted_crates": sorted(crates),
        "curated_crates": curated,
        "workspace_crates": workspace,
        "run_sidecar_curated": bool(curated),
        # Workspace-libs only when a non-curated/non-excluded package is touched.
        # Excluded-only crates (e.g. tool-broker) still get clippy from the parent call.
        "run_workspace_libs": bool(workspace),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".", help="Repository root")
    parser.add_argument("--base-ref", default="origin/main", help="Diff base ref")
    parser.add_argument(
        "--full-workspace",
        action="store_true",
        help="Force full workspace mode",
    )
    parser.add_argument("--output", help="Write JSON to this path")
    parser.add_argument(
        "--github-output",
        action="store_true",
        help="Also append key=value lines to $GITHUB_OUTPUT",
    )
    args = parser.parse_args()

    root = Path(args.root).resolve()
    files = get_changed_files(root, args.base_ref)
    result = build_result(files, args.full_workspace)

    text = json.dumps(result, indent=2)
    if args.output:
        Path(args.output).write_text(text + "\n", encoding="utf-8")
    print(text)

    if args.github_output:
        import os

        out = os.environ.get("GITHUB_OUTPUT")
        if not out:
            print("Warning: GITHUB_OUTPUT unset", file=sys.stderr)
            return 0
        with open(out, "a", encoding="utf-8") as fh:
            fh.write(f"full_workspace={'true' if result['full_workspace'] else 'false'}\n")
            fh.write(
                f"run_sidecar_curated={'true' if result['run_sidecar_curated'] else 'false'}\n"
            )
            fh.write(
                f"run_workspace_libs={'true' if result['run_workspace_libs'] else 'false'}\n"
            )
            fh.write(f"workspace_crates={' '.join(result['workspace_crates'])}\n")
            fh.write(f"curated_crates={' '.join(result['curated_crates'])}\n")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
