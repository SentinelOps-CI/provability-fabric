#!/usr/bin/env python3
"""Check formatting of tracked Go sources without modifying the worktree.

The root Makefile uses this program before go vet. Git enumerates checked-in
source files only, avoiding generated or untracked build products.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys

DEFAULT_MODULES = (
    "services/spec-service",
    "services/proof-service",
    "services/build-orchestrator",
    "services/evidence-service",
    "services/replay-service",
    "services/api-gateway",
)


class FormatCheckError(Exception):
    """The source-format check could not establish a passing result."""


def check_go_format(root: Path, modules: tuple[str, ...]) -> list[str]:
    """Return unformatted paths or raise for malformed inputs and tool failures.

    No formatter is invoked in write mode. Paths are selected from the Git
    index to prevent untracked, local-only files from influencing the result.
    """
    if not root.is_dir() or not modules:
        raise FormatCheckError("repository root and at least one module are required")
    for name in modules:
        path = Path(name)
        if path.is_absolute() or not path.parts or any(part == ".." for part in path.parts):
            raise FormatCheckError(f"invalid module path: {name!r}")
        if not (root / path).is_dir():
            raise FormatCheckError(f"missing module directory: {name}")
    try:
        scan = subprocess.run(
            ["git", "ls-files", "-z", "--", *modules],
            cwd=root, capture_output=True, check=True, timeout=30,
        )
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise FormatCheckError(f"unable to inspect tracked files: {type(exc).__name__}") from exc
    paths = [os.fsdecode(path) for path in scan.stdout.split(b"\0") if path.endswith(b".go")]
    if not paths:
        raise FormatCheckError("no tracked Go source files found for the selected modules")
    for path in paths:
        file = root / path
        if not file.is_file() or file.is_symlink():
            raise FormatCheckError(f"tracked Go source is missing or is a symlink: {path}")
    unformatted: list[str] = []
    try:
        # Bound the argument list for compatibility with Windows command limits.
        for start in range(0, len(paths), 50):
            result = subprocess.run(
                ["gofmt", "-l", *paths[start:start + 50]],
                cwd=root, capture_output=True, text=True, check=True, timeout=60,
            )
            if result.stderr.strip():
                raise FormatCheckError(f"gofmt issued diagnostics: {result.stderr.strip()}")
            unformatted.extend(line for line in result.stdout.splitlines() if line)
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise FormatCheckError(f"gofmt failed: {type(exc).__name__}") from exc
    return sorted(unformatted)


def main(argv: list[str] | None = None) -> int:
    """Check the Go services maintained by the root lint target."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("modules", nargs="*", default=list(DEFAULT_MODULES))
    args = parser.parse_args(argv)
    try:
        unformatted = check_go_format(args.root.resolve(), tuple(args.modules))
    except FormatCheckError as exc:
        print(f"Go formatting check blocked: {exc}", file=sys.stderr)
        return 2
    if unformatted:
        print("Unformatted Go sources (run gofmt -w on these files):", file=sys.stderr)
        for name in unformatted:
            print(f"  {name}", file=sys.stderr)
        return 1
    print("Tracked Go sources are gofmt-clean")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
