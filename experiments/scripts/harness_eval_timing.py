# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Parse SWE-bench harness per-instance test runtime from run_instance.log (eval output).

from __future__ import annotations

import re
import statistics
from pathlib import Path
from typing import Any

# SWE-bench eval logs this after running instance tests.
_TEST_RUNTIME_RE = re.compile(r"Test runtime:\s*([0-9.]+)\s*seconds", re.IGNORECASE)

_PARSE_NOTE = (
    "Seconds from run_instance.log line 'Test runtime: N seconds' (test phase in harness "
    "container; not full Docker wall-clock or agent time)."
)

_MAX_LOG_BYTES = 4 * 1024 * 1024


def _parse_test_runtime_seconds(log_path: Path) -> float | None:
    try:
        data = log_path.read_bytes()
        if len(data) > _MAX_LOG_BYTES:
            data = data[-_MAX_LOG_BYTES:]
        text = data.decode("utf-8", errors="replace")
    except OSError:
        return None
    m = _TEST_RUNTIME_RE.search(text)
    if not m:
        return None
    try:
        return float(m.group(1))
    except ValueError:
        return None


def _percentile_sorted(sorted_vals: list[float], p: float) -> float | None:
    if not sorted_vals:
        return None
    n = len(sorted_vals)
    if n == 1:
        return round(sorted_vals[0], 4)
    idx = min(max(int(round((p / 100.0) * (n - 1))), 0), n - 1)
    return round(sorted_vals[idx], 4)


def collect_harness_seconds_per_instance(eval_dir: Path) -> dict[str, float]:
    """
    Walk eval_dir/logs/run_evaluation/<run_id>/<model>/<instance_id>/run_instance.log.
    When multiple runs exist, keep the newest run batch (by run_id dir mtime) per instance.
    """
    root = eval_dir / "logs" / "run_evaluation"
    if not root.is_dir():
        return {}
    run_dirs = sorted(
        [p for p in root.iterdir() if p.is_dir()],
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    per_instance: dict[str, float] = {}
    for rd in run_dirs:
        try:
            model_dirs = [p for p in rd.iterdir() if p.is_dir()]
        except OSError:
            continue
        for model_dir in model_dirs:
            try:
                inst_dirs = [p for p in model_dir.iterdir() if p.is_dir()]
            except OSError:
                continue
            for inst_dir in inst_dirs:
                iid = inst_dir.name
                if iid in per_instance:
                    continue
                log = inst_dir / "run_instance.log"
                if not log.is_file():
                    continue
                sec = _parse_test_runtime_seconds(log)
                if sec is not None:
                    per_instance[iid] = round(sec, 4)
    return per_instance


def summarize_harness_eval_from_eval_dir(eval_dir: Path) -> dict[str, Any]:
    """Block for compare.json harness_eval.baseline / harness_eval.pf."""
    per = collect_harness_seconds_per_instance(eval_dir)
    vals = sorted(per.values())
    summary: dict[str, Any] | None = None
    if vals:
        summary = {
            "mean": round(sum(vals) / len(vals), 4),
            "median": round(statistics.median(vals), 4),
            "p90": _percentile_sorted(vals, 90.0),
            "p95": _percentile_sorted(vals, 95.0),
            "n": len(vals),
        }
    return {
        "harness_seconds_per_instance": per,
        "summary": summary,
        "parse_note": _PARSE_NOTE,
        "n_parsed": len(per),
    }
