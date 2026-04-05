#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Aggregate stress run into a single summary artifact for regression detection:
# timeout rates, wall-clock median/p95, guard overhead, solve rates, empty_patch_reasons, patch_apply.

from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from experiments.run_evidence import load_summary, load_timing, load_cost_report


def _percentile(sorted_arr: list[float], p: float) -> float | None:
    if not sorted_arr:
        return None
    idx = min(int(len(sorted_arr) * p / 100.0), len(sorted_arr) - 1)
    return sorted_arr[idx]


def _instance_ids_from_run(run_dir: Path) -> list[str]:
    summary = load_summary(run_dir)
    if not summary:
        return []
    instances = summary.get("instances") or []
    return [r.get("instance_id") for r in instances if r.get("instance_id")]


def _token_tool_stats(run_dir: Path, id_list: list[str]) -> dict[str, float | None]:
    """Median and p95 of total tokens (prompt+completion) and tool_calls from cost_report."""
    toks: list[float] = []
    tcalls: list[float] = []
    for iid in id_list:
        cr = load_cost_report(run_dir, iid)
        if not cr:
            continue
        toks.append(
            float(int(cr.get("prompt_tokens") or 0) + int(cr.get("completion_tokens") or 0))
        )
        tcalls.append(float(int(cr.get("tool_calls") or 0)))
    out: dict[str, float | None] = {
        "tokens_median": None,
        "tokens_p95": None,
        "tool_calls_median": None,
        "tool_calls_p95": None,
    }
    if toks:
        st = sorted(toks)
        out["tokens_median"] = round(statistics.median(st), 4)
        out["tokens_p95"] = round(_percentile(st, 95.0) or 0.0, 4)
    if tcalls:
        sc = sorted(tcalls)
        out["tool_calls_median"] = round(statistics.median(sc), 4)
        out["tool_calls_p95"] = round(_percentile(sc, 95.0) or 0.0, 4)
    return out


def _wall_clock_and_timeout(
    run_dir: Path, instance_id: str
) -> tuple[float | None, bool]:
    """Return (wall_clock_s, timeout_reached). Uses timing.json; fallback cost_report for wall_clock only."""
    timing = load_timing(run_dir, instance_id)
    if timing is not None:
        w = timing.get("wall_clock_s")
        wall = float(w) if w is not None else None
        timeout = bool(timing.get("timeout_reached"))
        if wall is None and "tool_calls" in timing:
            wall = 0.0  # allow zero
        return wall, timeout
    cost = load_cost_report(run_dir, instance_id)
    if cost is not None:
        w = cost.get("wall_clock_s")
        return (float(w) if w is not None else None), False
    return None, False


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Summarize baseline + PF stress run for regression detection (timeout rate, wall-clock, guard overhead).",
    )
    parser.add_argument("--baseline-run-dir", type=Path, required=True)
    parser.add_argument("--pf-run-dir", type=Path, required=True)
    parser.add_argument("--compare-json", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True, help="Output stress_summary.json path")
    parser.add_argument("--pf-commit", default="", help="PF repo commit (e.g. git rev-parse --short=12 HEAD)")
    parser.add_argument("--agent-commit", default="", help="Agent/image version (or leave empty to use compare.json openhands_version)")
    args = parser.parse_args()

    baseline_dir = args.baseline_run_dir.resolve()
    pf_dir = args.pf_run_dir.resolve()
    compare_path = args.compare_json.resolve()
    out_path = args.out.resolve()

    if not compare_path.exists():
        print("Error: compare.json not found: %s" % compare_path, file=sys.stderr)
        return 1

    try:
        compare = json.loads(compare_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print("Error: failed to load compare.json: %s" % e, file=sys.stderr)
        return 1

    # Instance lists
    baseline_ids = _instance_ids_from_run(baseline_dir)
    pf_ids = _instance_ids_from_run(pf_dir)
    all_ids = sorted(set(baseline_ids) | set(pf_ids))
    if not all_ids:
        # Fallback: no summary.json; write minimal summary from compare only
        out_path.parent.mkdir(parents=True, exist_ok=True)
        pa = compare.get("patch_apply") or {}
        b = compare.get("baseline") or {}
        p = compare.get("pf") or {}
        empty = compare.get("empty_patch_reasons_topN") or []
        stress_minimal = {
                    "schema_version": "1.0",
                    "pf_commit": args.pf_commit or None,
                    "agent_commit": compare.get("openhands_version"),
                    "dataset_id": compare.get("dataset_name"),
                    "dataset_version": compare.get("datasets_version"),
                    "harness_id": compare.get("harness_dataset_id") or compare.get("swebench_version"),
                    "message": "no run summary (summary.json missing in both run dirs)",
                    "baseline_solve_rate": b.get("solve_rate"),
                    "pf_solve_rate": p.get("solve_rate"),
                    "patch_apply_total": pa.get("total"),
                    "patch_apply_applies_false": pa.get("applies_false"),
                    "empty_patch_reasons_topN": empty,
                    "timeout_rate_baseline": None,
                    "timeout_rate_pf": None,
                    "wall_clock_s_median_baseline": None,
                    "wall_clock_s_median_pf": None,
                    "wall_clock_s_p95_baseline": None,
                    "wall_clock_s_p95_pf": None,
                    "guard_overhead_s_median": None,
                    "tokens_median_baseline": None,
                    "tokens_median_pf": None,
                    "tokens_p95_baseline": None,
                    "tokens_p95_pf": None,
                    "tool_calls_median_baseline": None,
                    "tool_calls_median_pf": None,
                    "tool_calls_p95_baseline": None,
                    "tool_calls_p95_pf": None,
                }
        out_path.write_text(json.dumps(stress_minimal, indent=2), encoding="utf-8")
        print("Wrote %s (no instance timing)" % out_path)
        return 0

    # Per-run timing
    baseline_walls: list[float] = []
    baseline_timeouts = 0
    pf_walls: list[float] = []
    pf_timeouts = 0
    paired_overheads: list[float] = []

    for iid in all_ids:
        b_wall, b_to = _wall_clock_and_timeout(baseline_dir, iid)
        p_wall, p_to = _wall_clock_and_timeout(pf_dir, iid)
        if iid in baseline_ids:
            if b_to:
                baseline_timeouts += 1
            if b_wall is not None:
                baseline_walls.append(b_wall)
        if iid in pf_ids:
            if p_to:
                pf_timeouts += 1
            if p_wall is not None:
                pf_walls.append(p_wall)
        if b_wall is not None and p_wall is not None and iid in baseline_ids and iid in pf_ids:
            paired_overheads.append(p_wall - b_wall)

    n_baseline = len(baseline_ids) or 1
    n_pf = len(pf_ids) or 1
    timeout_rate_baseline = baseline_timeouts / n_baseline if baseline_ids else None
    timeout_rate_pf = pf_timeouts / n_pf if pf_ids else None

    def med(vals: list[float]) -> float | None:
        if not vals:
            return None
        return round(statistics.median(vals), 4)

    def p95(vals: list[float]) -> float | None:
        if not vals:
            return None
        s = sorted(vals)
        return round(_percentile(s, 95.0) or 0.0, 4)

    pa = compare.get("patch_apply") or {}
    b = compare.get("baseline") or {}
    p = compare.get("pf") or {}
    empty = compare.get("empty_patch_reasons_topN") or []

    bs_tok = _token_tool_stats(baseline_dir, baseline_ids)
    pf_tok = _token_tool_stats(pf_dir, pf_ids)
    stress = {
        "schema_version": "1.0",
        "pf_commit": args.pf_commit or None,
        "agent_commit": args.agent_commit or compare.get("openhands_version"),
        "dataset_id": compare.get("dataset_name"),
        "dataset_version": compare.get("datasets_version"),
        "harness_id": compare.get("harness_dataset_id") or compare.get("swebench_version"),
        "timeout_rate_baseline": round(timeout_rate_baseline, 6) if timeout_rate_baseline is not None else None,
        "timeout_rate_pf": round(timeout_rate_pf, 6) if timeout_rate_pf is not None else None,
        "wall_clock_s_median_baseline": med(baseline_walls),
        "wall_clock_s_median_pf": med(pf_walls),
        "wall_clock_s_p95_baseline": p95(baseline_walls),
        "wall_clock_s_p95_pf": p95(pf_walls),
        "guard_overhead_s_median": med(paired_overheads),
        "tokens_median_baseline": bs_tok["tokens_median"],
        "tokens_median_pf": pf_tok["tokens_median"],
        "tokens_p95_baseline": bs_tok["tokens_p95"],
        "tokens_p95_pf": pf_tok["tokens_p95"],
        "tool_calls_median_baseline": bs_tok["tool_calls_median"],
        "tool_calls_median_pf": pf_tok["tool_calls_median"],
        "tool_calls_p95_baseline": bs_tok["tool_calls_p95"],
        "tool_calls_p95_pf": pf_tok["tool_calls_p95"],
        "empty_patch_reasons_topN": empty,
        "patch_apply_total": pa.get("total"),
        "patch_apply_applies_false": pa.get("applies_false"),
        "baseline_solve_rate": b.get("solve_rate"),
        "pf_solve_rate": p.get("solve_rate"),
        "n_instances_baseline": len(baseline_ids),
        "n_instances_pf": len(pf_ids),
    }

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(stress, indent=2), encoding="utf-8")
    print("Wrote %s" % out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
