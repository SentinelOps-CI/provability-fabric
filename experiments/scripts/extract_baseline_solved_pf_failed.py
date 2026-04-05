#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Identify "baseline solved, PF failed" from compare.csv and extract for each:
# - policy_compliance_summary.json
# - top 20 lines around the first violation in events.jsonl
# - last ~50 lines of OpenHands trace (run.log)
# Output written to <out-dir>/<instance_id>/ for iteration debugging.

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path
from typing import Any

# Ensure repo root on path
_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from bench.swebench.util import sanitize_instance_id
from experiments.harness_report import find_run_report, get_resolved_ids, load_run_report

CONTEXT_LINES = 20
TRACE_TAIL_LINES = 50


def get_baseline_solved_pf_failed_from_csv(compare_csv: Path) -> list[str]:
    """From compare.csv filter baseline_resolved=1, pf_resolved=0. Skip _summary."""
    if not compare_csv.exists():
        return []
    ids: list[str] = []
    with open(compare_csv, newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            iid = row.get("instance_id", "").strip()
            if iid == "" or iid == "_summary":
                continue
            try:
                b = int(row.get("baseline_resolved", 0))
                p = int(row.get("pf_resolved", 1))
            except (ValueError, TypeError):
                continue
            if b == 1 and p == 0:
                ids.append(iid)
    return ids


def get_baseline_solved_pf_failed_from_harness(
    baseline_eval_dir: Path, pf_eval_dir: Path
) -> list[str]:
    """Fallback: compute set from harness reports when compare.csv has no per-instance rows."""
    br_path = find_run_report(baseline_eval_dir)
    pr_path = find_run_report(pf_eval_dir)
    if not br_path or not pr_path:
        return []
    br = load_run_report(br_path)
    pr = load_run_report(pr_path)
    if not br or not pr:
        return []
    baseline_resolved = get_resolved_ids(br)
    pf_resolved = get_resolved_ids(pr)
    return sorted(baseline_resolved - pf_resolved)


def extract_first_violation_context(events_path: Path, context: int = CONTEXT_LINES) -> str:
    """Return up to context lines before and after the first violation event (JSONL)."""
    if not events_path.exists():
        return "(events.jsonl not found)"
    lines = events_path.read_text(encoding="utf-8", errors="replace").splitlines()
    violation_idx = -1
    for i, line in enumerate(lines):
        line = line.strip()
        if not line:
            continue
        try:
            ev = json.loads(line)
            if ev.get("event_type") == "violation":
                violation_idx = i
                break
        except json.JSONDecodeError:
            continue
    if violation_idx < 0:
        return "(no violation event in events.jsonl)"
    start = max(0, violation_idx - context)
    end = min(len(lines), violation_idx + context + 1)
    return "\n".join(lines[start:end])


def extract_trace_tail(run_log_path: Path, tail_lines: int = TRACE_TAIL_LINES) -> str:
    """Last tail_lines of run.log (OpenHands/tool trace)."""
    if not run_log_path.exists():
        return "(run.log not found)"
    lines = run_log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    if len(lines) <= tail_lines:
        return "\n".join(lines)
    return "\n".join(lines[-tail_lines:])


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract artifacts for 'baseline solved, PF failed' instances for iteration debugging.",
    )
    parser.add_argument(
        "--compare-csv",
        type=Path,
        default=Path("runs/exp-step2-lite-smoke/compare.csv"),
        help="compare.csv from compare_runs.py",
    )
    parser.add_argument(
        "--pf-run-dir",
        type=Path,
        required=True,
        help="PF run dir (e.g. runs/exp-step2-lite-smoke/pf/<run_id>)",
    )
    parser.add_argument(
        "--experiment-dir",
        type=Path,
        default=Path("runs/exp-step2-lite-smoke"),
        help="Experiment dir (for fallback: baseline/eval, pf/eval)",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("runs/exp-step2-lite-smoke/debug_baseline_solved_pf_failed"),
        help="Output directory; one subdir per instance_id",
    )
    parser.add_argument(
        "--context-lines",
        type=int,
        default=CONTEXT_LINES,
        help="Lines around first violation in events.jsonl",
    )
    parser.add_argument(
        "--trace-tail-lines",
        type=int,
        default=TRACE_TAIL_LINES,
        help="Last N lines of run.log to capture",
    )
    args = parser.parse_args()

    instance_ids = get_baseline_solved_pf_failed_from_csv(args.compare_csv)
    if not instance_ids:
        baseline_eval = args.experiment_dir / "baseline" / "eval"
        pf_eval = args.experiment_dir / "pf" / "eval"
        instance_ids = get_baseline_solved_pf_failed_from_harness(baseline_eval, pf_eval)
    if not instance_ids:
        print("No 'baseline solved, PF failed' instances found.", file=sys.stderr)
        return 0

    args.out_dir.mkdir(parents=True, exist_ok=True)
    for iid in instance_ids:
        sanitized = sanitize_instance_id(iid)
        inst_dir = Path(args.pf_run_dir) / sanitized
        out_inst = args.out_dir / sanitized
        out_inst.mkdir(parents=True, exist_ok=True)

        # 1) policy_compliance_summary.json
        comp_path = inst_dir / "policy_compliance_summary.json"
        if comp_path.exists():
            (out_inst / "policy_compliance_summary.json").write_text(
                comp_path.read_text(encoding="utf-8"), encoding="utf-8"
            )

        # 2) Top 20 lines around first violation in events.jsonl
        events_path = inst_dir / "evidence" / "events.jsonl"
        context = extract_first_violation_context(events_path, context=args.context_lines)
        (out_inst / "events_first_violation_context.txt").write_text(
            context, encoding="utf-8"
        )

        # 3) Last ~50 lines of OpenHands trace (run.log)
        run_log_path = inst_dir / "run.log"
        trace_tail = extract_trace_tail(run_log_path, tail_lines=args.trace_tail_lines)
        (out_inst / "run_log_tail.txt").write_text(trace_tail, encoding="utf-8")

    index_path = args.out_dir / "instance_ids.txt"
    index_path.write_text("\n".join(instance_ids) + "\n", encoding="utf-8")
    print(f"Extracted {len(instance_ids)} instances to {args.out_dir}")
    print(f"Instance list: {index_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
