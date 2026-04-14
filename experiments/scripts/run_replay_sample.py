#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# After a successful PF run + harness: select N instances where harness resolved
# and PF compliance shows violations == 0 on final patch; run replay and write
# replay_summary.json (sample_size, success_rate, mismatch_count, replay_fail_reasons_topN).

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
from collections import Counter
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from experiments.harness_report import find_run_report, load_run_report
from experiments.run_evidence import load_compliance

RESOLVED_IDS = "resolved_ids"


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run replay on a sample of PF-resolved, zero-violation instances; write replay_summary.json.",
    )
    parser.add_argument("--pf-eval-dir", type=Path, required=True, help="PF eval dir (harness report)")
    parser.add_argument("--pf-run-dir", type=Path, required=True, help="PF run dir (runs/exp/.../pf/<run_id>)")
    parser.add_argument("--runs-dir", type=Path, default=None, help="Runs root (default: parent of pf-run-dir twice)")
    parser.add_argument("--max-sample", type=int, default=5, help="Max instances to replay when sample < full (default 5)")
    parser.add_argument("--replay-all-if-le", type=int, default=20, help="If PF-resolved with violations==0 count <= this, replay all (default 20)")
    parser.add_argument("--sample-size-scheduled", type=int, default=40, help="When replaying a sample (count > replay_all_if_le), use this size (default 40)")
    parser.add_argument("--seed", type=int, default=42, help="Seed for deterministic sample when not replaying all")
    parser.add_argument("--out", type=Path, default=None, help="Write replay_summary.json here (default: pf-eval-dir/../replay_summary.json)")
    parser.add_argument("--replay-dir", type=Path, default=None, help="Write replay/instance_results.jsonl here (default: same dir as --out, under replay/)")
    parser.add_argument("--replay-cmd", type=str, default="pf", help="Command for replay: pf or python (default pf)")
    args = parser.parse_args()

    pf_eval_dir = args.pf_eval_dir.resolve()
    pf_run_dir = args.pf_run_dir.resolve()
    if not pf_run_dir.is_dir():
        print("Error: PF run dir not found: %s" % pf_run_dir, file=sys.stderr)
        return 1
    run_id = pf_run_dir.name
    # runs_dir = dir containing run_id (e.g. runs/exp_step2_lite_smoke/pf)
    runs_dir = args.runs_dir.resolve() if args.runs_dir else pf_run_dir.parent
    out_path = (args.out.resolve() if args.out else pf_eval_dir.parent / "replay_summary.json")

    # Resolved IDs from harness
    report_path = find_run_report(pf_eval_dir)
    if not report_path or not report_path.exists():
        print("Error: No harness report in %s" % pf_eval_dir, file=sys.stderr)
        return 1
    report = load_run_report(report_path)
    if not report:
        print("Error: Invalid harness report", file=sys.stderr)
        return 1
    resolved = set(report.get(RESOLVED_IDS, []))

    # Filter: resolved and violations == 0
    candidates = []
    for iid in resolved:
        comp = load_compliance(pf_run_dir, iid)
        if not comp:
            continue
        violations = int(comp.get("violations") or comp.get("total_violations") or 0)
        if violations == 0:
            candidates.append(iid)
    # Replay coverage: all when count <= replay_all_if_le, else deterministic sample (25-50)
    if len(candidates) <= args.replay_all_if_le:
        sample = sorted(candidates)
    else:
        rng = random.Random(args.seed)
        size = min(len(candidates), max(25, args.sample_size_scheduled))
        sample = sorted(rng.sample(candidates, size))
    if not sample:
        summary = {
            "sample_size": 0,
            "success_rate": None,
            "mismatch_count": 0,
            "replay_fail_reasons_topN": [],
            "message": "No instances with harness resolved and violations==0",
        }
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
        print("No sample instances; wrote %s with sample_size=0" % out_path)
        return 0

    # Run replay
    instance_ids_str = ",".join(sample)
    cmd = [args.replay_cmd, "bench", "swebench", "replay", "--run_id", run_id, "--instance-ids", instance_ids_str, "--runs-dir", str(runs_dir), "--json"]
    if args.replay_cmd == "python":
        cmd = [
            sys.executable,
            str(_REPO_ROOT / "bench" / "swebench" / "run_replay.py"),
            "--run-id", run_id,
            "--instance-ids", instance_ids_str,
            "--runs-dir", str(runs_dir),
            "--json",
        ]
    try:
        proc = subprocess.run(cmd, cwd=str(_REPO_ROOT), capture_output=True, text=True, timeout=600)
        out_json = proc.stdout
        if proc.returncode != 0 and not out_json:
            print("Error: Replay failed: %s" % (proc.stderr or "no output"), file=sys.stderr)
            return 1
    except (FileNotFoundError, subprocess.TimeoutExpired) as e:
        print("Error: Replay failed: %s" % e, file=sys.stderr)
        return 1

    try:
        data = json.loads(out_json)
    except json.JSONDecodeError as e:
        print("Error: Replay output not JSON: %s" % e, file=sys.stderr)
        return 1

    results = data.get("results") or []
    success_count = sum(1 for r in results if r.get("success") and r.get("match"))
    mismatch_count = len(results) - success_count
    reason_counter: Counter[str] = Counter()
    for r in results:
        if not (r.get("success") and r.get("match")):
            msg = (r.get("message") or "unknown").strip()[:200]
            reason_counter[msg] += 1

    summary = {
        "sample_size": len(results),
        "success_rate": round(success_count / len(results), 6) if results else None,
        "mismatch_count": mismatch_count,
        "replay_fail_reasons_topN": [{"reason": r, "count": c} for r, c in reason_counter.most_common(10)],
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print("Wrote %s (sample_size=%d, success_rate=%s)" % (out_path, summary["sample_size"], summary["success_rate"]))

    # Per-instance results for audit (replay/instance_results.jsonl)
    replay_dir = args.replay_dir.resolve() if args.replay_dir else out_path.parent / "replay"
    replay_dir.mkdir(parents=True, exist_ok=True)
    instance_results_path = replay_dir / "instance_results.jsonl"
    with open(instance_results_path, "w", encoding="utf-8") as f:
        for r in results:
            rec = {
                "instance_id": r.get("instance_id"),
                "success": r.get("success"),
                "match": r.get("match"),
                "replay_ok": bool(r.get("success") and r.get("match")),
                "original_patch_sha256": r.get("original_patch_sha256"),
                "reconstituted_patch_sha256": r.get("reconstituted_patch_sha256"),
                "failure_reason": None if (r.get("success") and r.get("match")) else (r.get("message") or "unknown"),
            }
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
    print("Wrote %s (%d lines)" % (instance_results_path, len(results)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
