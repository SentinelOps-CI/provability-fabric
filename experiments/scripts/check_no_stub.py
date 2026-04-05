#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Fail the run if any model.patch under the given run dirs contains .swebench_stub.
# Use after baseline and PF runs; if this exits non-zero, the run must be considered failed.

from __future__ import annotations

import argparse
import sys
from pathlib import Path

STUB_MARKER = ".swebench_stub"


def check_run_dir(run_root: Path) -> list[tuple[Path, str]]:
    """
    Scan run_root (e.g. runs/exp-step2-lite-smoke/baseline) for run_id subdirs.
    Under each run_id, check every instance dir's model.patch for STUB_MARKER.
    Returns list of (path, line_preview) for each violation.
    """
    violations: list[tuple[Path, str]] = []
    if not run_root.is_dir():
        return violations
    for run_id_dir in run_root.iterdir():
        if not run_id_dir.is_dir() or run_id_dir.name.startswith("."):
            continue
        for inst_dir in run_id_dir.iterdir():
            if not inst_dir.is_dir():
                continue
            patch_file = inst_dir / "model.patch"
            if not patch_file.exists():
                continue
            try:
                text = patch_file.read_text(encoding="utf-8", errors="replace")
                if STUB_MARKER in text:
                    first_line = text.splitlines()[0] if text.strip() else "(empty)"
                    violations.append((patch_file, first_line[:80]))
            except OSError:
                pass
    return violations


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Fail if any model.patch under run dirs contains .swebench_stub (run must be considered failed).",
    )
    parser.add_argument(
        "run_dirs",
        nargs="+",
        type=Path,
        help="Run root dirs (e.g. runs/exp-step2-lite-smoke/baseline runs/exp-step2-lite-smoke/pf)",
    )
    args = parser.parse_args()
    all_violations: list[tuple[Path, str]] = []
    for run_root in args.run_dirs:
        all_violations.extend(check_run_dir(run_root))
    if not all_violations:
        return 0
    print("ERROR: .swebench_stub found in model.patch; run must be considered failed.", file=sys.stderr)
    for path, preview in all_violations:
        print(f"  {path}: {preview!r}", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
