# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Shared helpers for reading SWE-bench harness run reports (eval dir JSON).

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

RESOLVED_IDS = "resolved_ids"
UNRESOLVED_IDS = "unresolved_ids"
ERROR_IDS = "error_ids"
EMPTY_PATCH_IDS = "empty_patch_ids"
TOTAL_INSTANCES = "total_instances"
RESOLVED_INSTANCES = "resolved_instances"
UNRESOLVED_INSTANCES = "unresolved_instances"
ERROR_INSTANCES = "error_instances"


def find_run_report(eval_dir: Path) -> Path | None:
    """Return the newest harness run-report JSON in eval_dir.

    Multiple reports accumulate across re-runs (one file per run_id).  Always
    returning the *newest* by mtime ensures compare and the stale-eval check
    operate on the most recent harness execution rather than an arbitrary
    (possibly stale) earlier one.
    """
    p = Path(eval_dir)
    if not p.is_dir():
        return None
    candidates: list[tuple[float, Path]] = []
    for f in p.iterdir():
        if f.suffix == ".json" and f.is_file():
            try:
                data = json.loads(f.read_text(encoding="utf-8"))
                if isinstance(data, dict) and (
                    RESOLVED_IDS in data or RESOLVED_INSTANCES in data
                ):
                    candidates.append((f.stat().st_mtime, f))
            except (json.JSONDecodeError, OSError):
                continue
    if not candidates:
        return None
    # Return the most recently written report.
    candidates.sort(key=lambda t: t[0], reverse=True)
    return candidates[0][1]


def load_run_report(path: Path) -> dict[str, Any] | None:
    """Load and return run report dict, or None if invalid."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        if isinstance(data, dict) and (
            RESOLVED_IDS in data or RESOLVED_INSTANCES in data
        ):
            return data
    except (json.JSONDecodeError, OSError):
        pass
    return None


def get_resolved_ids(report: dict[str, Any]) -> set[str]:
    """Return set of resolved instance IDs from a loaded report."""
    return set(report.get(RESOLVED_IDS, report.get(RESOLVED_INSTANCES, [])))
