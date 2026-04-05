#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Check stress_summary.json and compare.json against regression thresholds.
# Single source of truth for stress alert logic (used by workflow and run_verification_tests).

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_DEFAULT_CONFIG = _SCRIPT_DIR.parent / "config" / "stress_alerts.yaml"

DEFAULT_THRESHOLDS = {
    "parity_threshold": 0.01,
    "timeout_delta_threshold": 0.25,
    "empty_patch_rate_threshold": 0.45,
    "guard_overhead_s_threshold": 180.0,
}


def load_thresholds(config_path: Path | None) -> dict[str, float]:
    """Load thresholds from YAML; fall back to DEFAULT_THRESHOLDS if file missing or invalid."""
    out = dict(DEFAULT_THRESHOLDS)
    path = config_path or _DEFAULT_CONFIG
    if not path.exists():
        return out
    try:
        import yaml
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
        for k, v in data.items():
            if k in out and isinstance(v, (int, float)):
                out[k] = float(v)
    except Exception:
        pass
    return out


def check(
    stress: dict,
    compare: dict,
    thresholds: dict[str, float] | None = None,
) -> list[str]:
    """Return list of failure messages (empty if all thresholds OK)."""
    th = thresholds or load_thresholds(None)
    failed: list[str] = []
    bl = compare.get("baseline") or {}
    pf = compare.get("pf") or {}
    bl_rate = bl.get("solve_rate")
    pf_rate = pf.get("solve_rate")
    parity = th["parity_threshold"]
    if bl_rate is not None and pf_rate is not None and pf_rate < bl_rate - parity:
        failed.append(
            "PARITY: pf.solve_rate (%s) < baseline.solve_rate (%s) - %s"
            % (pf_rate, bl_rate, parity)
        )
    to_bl = stress.get("timeout_rate_baseline") or 0
    to_pf = stress.get("timeout_rate_pf") or 0
    to_delta = th["timeout_delta_threshold"]
    if to_pf - to_bl > to_delta:
        failed.append(
            "TIMEOUT_DELTA: timeout_rate_pf - timeout_rate_baseline = %s > %s"
            % (to_pf - to_bl, to_delta)
        )
    pa = compare.get("patch_apply") or {}
    total = pa.get("total") or 0
    applies_false = pa.get("applies_false") or 0
    empty_th = th["empty_patch_rate_threshold"]
    if total > 0 and (applies_false / total) > empty_th:
        failed.append(
            "EMPTY_PATCH: applies_false/total = %s > %s"
            % (applies_false / total, empty_th)
        )
    overhead = stress.get("guard_overhead_s_median")
    guard_th = th["guard_overhead_s_threshold"]
    if overhead is not None and overhead > guard_th:
        failed.append(
            "GUARD_OVERHEAD: guard_overhead_s_median = %s > %s"
            % (overhead, guard_th)
        )
    return failed


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Check stress_summary and compare.json against regression thresholds.",
    )
    ap.add_argument("--stress-summary", type=Path, required=True, help="Path to stress_summary.json")
    ap.add_argument("--compare-json", type=Path, required=True, help="Path to compare.json")
    ap.add_argument("--config", type=Path, default=None, help="Optional stress_alerts.yaml (default: experiments/config/stress_alerts.yaml)")
    args = ap.parse_args()

    if not args.stress_summary.exists():
        print("STRESS_ALERT: stress summary not found: %s" % args.stress_summary, file=sys.stderr)
        return 1
    if not args.compare_json.exists():
        print("STRESS_ALERT: compare.json not found: %s" % args.compare_json, file=sys.stderr)
        return 1

    try:
        stress = json.loads(args.stress_summary.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print("STRESS_ALERT: failed to load stress summary: %s" % e, file=sys.stderr)
        return 1
    try:
        compare = json.loads(args.compare_json.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print("STRESS_ALERT: failed to load compare.json: %s" % e, file=sys.stderr)
        return 1

    thresholds = load_thresholds(args.config)
    failed = check(stress, compare, thresholds)
    for msg in failed:
        print("STRESS_ALERT: %s" % msg, file=sys.stderr)
    if failed:
        return 1
    print("Stress regression alerts: all thresholds OK.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
