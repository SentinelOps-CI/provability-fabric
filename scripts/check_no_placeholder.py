#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# P1 gate: scan repo for forbidden placeholder/stub patterns.
# Allowlisted paths (docs/internal/placeholders/placeholder-burn-down-allowlist.txt) are skipped.
# Exit 0 if no forbidden patterns; 1 otherwise.

from __future__ import annotations

import os
import re
import sys
from pathlib import Path


# Paths to skip entirely (generated, vendored, lockfiles with known placeholder versions)
SKIP_DIRS = {
    ".git",
    "node_modules",
    "target",
    "build",
    "dist",
    "site",
    "__pycache__",
    ".venv",
    "venv",
    "vendor",
    "mathlib",
    ".cursor",
}
SKIP_FILES = {
    "package-lock.json",
    "Cargo.lock",
    "go.sum",
    "predictions.jsonl",
    "predictions_fixture.jsonl",
    "evidence-service",
    "evidence-service.exe",
}
# Skip output/generated dirs (runs/ may contain stub patches from SWE-bench)
SKIP_PATH_PREFIXES = ("runs/", "bench/swebench/workspaces/", "workspaces/")
# Paths to never scan (gate script itself; build artifacts)
GATE_SKIP_PATHS = frozenset({
    "scripts/check_no_placeholder.py",
    "services/evidence-service/evidence-service",
    "services/evidence-service/evidence-service.exe",
    "core/cli/pf/pf",
    "core/cli/pf/pf.exe",
})


# Forbidden patterns: (regex, description). Applied to line content.
FORBIDDEN = [
    (re.compile(r'"placeholder-hash"'), "literal placeholder-hash"),
    (re.compile(r'"dsse:placeholder"'), "dsse:placeholder fallback"),
    (re.compile(r'placeholder-(?:policy|proof|automata|labeler)-hash'), "placeholder-*-hash in cert/middleware"),
    (re.compile(r'placeholder-policy-hash|placeholder-proof-hash|placeholder-automata-hash|placeholder-labeler-hash'), "placeholder hash in adapters"),
    (re.compile(r'vec!\[0u8;\s*32\].*[Pp]laceholder|[Pp]laceholder\s+key'), "placeholder signing key"),
    (re.compile(r'return true as a placeholder|For now, return true as a placeholder'), "return true as placeholder"),
    (re.compile(r'rollback_checksum_placeholder'), "rollback_checksum_placeholder in migration"),
    (re.compile(r'_stub_openhands_patch|_stub_generic_patch'), "stub patch engine"),
    (re.compile(r'placeholder-sha256-digest|"signature":\s*"placeholder"|"replay_drift":\s*"placeholder"|"bundle_id":\s*"placeholder'), "summarize placeholders"),
    (re.compile(r'BundleHash:\s*"placeholder-hash"'), "CLI fixture BundleHash placeholder"),
    (re.compile(r'policy_hash_placeholder|automata_hash_placeholder|labeler_hash_placeholder|dfa_hash_placeholder|plan_hash_placeholder|ni_monitor_hash_placeholder|resource_placeholder|attestation_token_placeholder|attestation_sig_placeholder'), "sidecar *_placeholder literals"),
    (re.compile(r'kms signer not implemented|vault signer not implemented'), "evidence-service kms/vault not implemented"),
    (re.compile(r'"proof":\s*"placeholder"|"conformance\.md".*Placeholder'), "evidence-service placeholder compliance files"),
    (re.compile(r'# Placeholder patch|# Stub patch from PF runner'), "SWE-bench stub patch comment in output"),
    (re.compile(r'For now, return a placeholder'), "Lean/code placeholder return"),
    (re.compile(r'Placeholder implementations for other validation'), "MPC compliance placeholder"),
    (re.compile(r'placeholder event processing|Process event \(placeholder|Process individual event \(placeholder\)'), "concurrency placeholder"),
    (re.compile(r'placeholder for Redis|TODO: Implement Redis'), "policy-kernel Redis placeholder"),
    (re.compile(r'TODO: Implement actual signature verification'), "signature verification TODO in engine/plan/broker"),
    (re.compile(r'Simple aggregation stub'), "platform_commands aggregation stub"),
    (re.compile(r'For now, return a placeholder'), "wasm_pool placeholder"),
    (re.compile(r'not yet implemented'), "impacted_only build impacted proofs"),
    (re.compile(r'replay.*echo.*todo|echo "todo"'), "create-sentinel-app replay todo"),
]

# Comment-only lines containing these are ignored for any pattern (EX-001)
EXCUSE_COMMENT_SUBSTRINGS = ("test stub", "unit test stub", "Synchronous unit test stub")


def load_placeholderignore(repo_root: Path) -> set[str]:
    path = repo_root / ".placeholderignore"
    if not path.exists():
        return set()
    patterns: set[str] = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            patterns.add(line.rstrip("/"))
    return patterns


def path_matches_placeholderignore(rel_path: str, patterns: set[str]) -> bool:
    norm = rel_path.replace("\\", "/")
    for pattern in patterns:
        if pattern.startswith("*."):
            if norm.endswith(pattern[1:]):
                return True
            continue
        if norm == pattern or norm.startswith(pattern + "/"):
            return True
    return False


def is_probably_binary(path: Path) -> bool:
    try:
        with open(path, "rb") as f:
            head = f.read(8192)
    except OSError:
        return True
    if not head:
        return False
    if b"\x00" in head[:1024]:
        return True
    if head[:4] == b"\x7fELF" or head[:2] == b"MZ":
        return True
    return False


def load_allowlist(repo_root: Path) -> set[str]:
    for subpath in (
        "docs/internal/placeholders/placeholder-burn-down-allowlist.txt",
        "docs/placeholder-burn-down-allowlist.txt",
    ):
        allowlist_path = repo_root / subpath
        if allowlist_path.exists():
            break
    else:
        return set()
    allowed = set()
    with open(allowlist_path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line and not line.startswith("#"):
                allowed.add(line)
    return allowed


def path_is_allowlisted(rel_path: str, allowlist: set[str]) -> bool:
    for prefix in allowlist:
        if rel_path == prefix or rel_path.startswith(prefix + "/"):
            return True
    return False


def is_comment_only(line: str, path: str) -> bool:
    stripped = line.strip()
    if not stripped:
        return True
    if stripped.startswith("//") or stripped.startswith("#") or stripped.startswith("*") or stripped.startswith("/*"):
        return True
    if stripped.startswith("*") and "*/" in stripped:
        return True
    return False


def line_has_excuse_comment(line: str) -> bool:
    lower = line.lower()
    return any(s in lower for s in EXCUSE_COMMENT_SUBSTRINGS)


def should_skip_path(rel_path: str) -> bool:
    norm = rel_path.replace("\\", "/")
    if norm in GATE_SKIP_PATHS:
        return True
    if norm.endswith(".exe"):
        return True
    parts = norm.split("/")
    if parts and parts[-1] in {"pf", "evidence-service"}:
        if norm.startswith("core/cli/pf/") or norm.startswith("services/evidence-service/"):
            return True
    for prefix in SKIP_PATH_PREFIXES:
        if norm.startswith(prefix):
            return True
    if any(p in SKIP_DIRS for p in parts):
        return True
    if parts and parts[-1] in SKIP_FILES:
        return True
    return False


def check_file(
    repo_root: Path,
    rel_path: str,
    allowlist: set[str],
    placeholderignore: set[str],
) -> list[tuple[int, str, str]]:
    hits = []
    if path_is_allowlisted(rel_path, allowlist):
        return hits
    if path_matches_placeholderignore(rel_path, placeholderignore):
        return hits
    if should_skip_path(rel_path):
        return hits
    path = repo_root / rel_path
    if not path.is_file():
        return hits
    if is_probably_binary(path):
        return hits
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            for i, line in enumerate(f, 1):
                if is_comment_only(line, rel_path) and line_has_excuse_comment(line):
                    continue
                for pattern, desc in FORBIDDEN:
                    if pattern.search(line):
                        hits.append((i, desc, line.strip()[:80]))
                        break
    except OSError:
        pass
    return hits


def main() -> int:
    repo_root = Path(__file__).resolve().parent.parent
    allowlist = load_allowlist(repo_root)
    placeholderignore = load_placeholderignore(repo_root)
    total_hits = []
    for root, _dirs, files in os.walk(repo_root, topdown=True):
        _dirs[:] = [d for d in _dirs if d not in SKIP_DIRS and not d.startswith(".")]
        try:
            rel_root = Path(root).relative_to(repo_root)
        except ValueError:
            continue
        rel_root_str = str(rel_root).replace("\\", "/")
        if any(rel_root_str.startswith(p) for p in SKIP_PATH_PREFIXES):
            _dirs.clear()
            continue
        for name in files:
            if name in SKIP_FILES:
                continue
            abs_path = Path(root) / name
            try:
                rel = abs_path.relative_to(repo_root)
            except ValueError:
                continue
            rel_str = str(rel).replace("\\", "/")
            if rel_str.startswith(".") or ".." in rel_str:
                continue
            for line_no, desc, snippet in check_file(
                repo_root, rel_str, allowlist, placeholderignore
            ):
                total_hits.append((rel_str, line_no, desc, snippet))
    if total_hits:
        print("no-runtime-placeholders: forbidden placeholder/stub patterns found:", file=sys.stderr)
        for path, line_no, desc, snippet in total_hits:
            print(f"  {path}:{line_no} ({desc})", file=sys.stderr)
            print(f"    {snippet}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
