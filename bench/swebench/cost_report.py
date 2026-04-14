# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Cost accounting: unified CostReport per instance and aggregate summary
# for "$ per solved issue" and comparing baseline vs PF-guarded OpenHands.

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

try:
    from bench.swebench.constants import COST_REPORT_FILENAME, SUMMARY_JSON_FILENAME
except ImportError:
    # When invoked as `python bench/swebench/runner.py`, sys.path may omit repo root;
    # cost_report must still load so per-instance cost_report.json is written.
    from constants import COST_REPORT_FILENAME, SUMMARY_JSON_FILENAME  # type: ignore[no-redef]

SUMMARY_CSV_FILENAME = "summary.csv"


def build_cost_report(
    instance_id: str,
    model_name: str,
    prompt_tokens: int = 0,
    completion_tokens: int = 0,
    iterations: int = 0,
    tool_calls: int = 0,
    wall_clock_s: float = 0.0,
    replay_s: float = 0.0,
    proof_s: float = 0.0,
    guarded: bool = False,
    run_id: str = "",
    engine_error: Optional[str] = None,
) -> dict:
    """Build a unified CostReport dict for one instance (and run-level replay_s, proof_s)."""
    out = {
        "instance_id": instance_id,
        "run_id": run_id,
        "guarded": guarded,
        "model_name": model_name,
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "iterations": iterations,
        "tool_calls": tool_calls,
        "wall_clock_s": round(wall_clock_s, 4),
        "replay_s": round(replay_s, 4),
        "proof_s": round(proof_s, 4),
    }
    if engine_error is not None:
        out["engine_error"] = engine_error
    return out


def write_cost_report(instance_dir: Path, report: dict) -> None:
    """Write runs/<run_id>/<instance_id>/cost_report.json."""
    instance_dir = Path(instance_dir)
    instance_dir.mkdir(parents=True, exist_ok=True)
    (instance_dir / COST_REPORT_FILENAME).write_text(
        json.dumps(report, indent=2),
        encoding="utf-8",
    )


def write_summary(run_dir: Path, reports: List[dict], run_id: str, guarded: bool) -> None:
    """Write runs/<run_id>/summary.json and summary.csv for easy comparison across runs."""
    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)

    summary = {
        "run_id": run_id,
        "guarded": guarded,
        "n_instances": len(reports),
        "instances": reports,
    }
    (run_dir / SUMMARY_JSON_FILENAME).write_text(
        json.dumps(summary, indent=2),
        encoding="utf-8",
    )

    if not reports:
        return
    # Union of keys across reports (some rows may include optional fields like engine_error).
    keys: list[str] = []
    for rec in reports:
        for k in rec.keys():
            if k not in keys:
                keys.append(k)
    with open(run_dir / SUMMARY_CSV_FILENAME, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=keys)
        w.writeheader()
        w.writerows(reports)
