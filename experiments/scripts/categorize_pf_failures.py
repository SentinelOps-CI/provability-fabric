#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Categorize PF failures into exactly one primary cause per instance (when PF
# solve rate drops vs baseline). Consumes baseline/pf eval reports and PF run
# evidence. Outputs categorization JSON and CSV for fix strategy selection.

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Optional

# Ensure repo root on path
_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from experiments.harness_report import (
    find_run_report,
    get_resolved_ids,
    load_run_report,
)
from experiments.run_evidence import load_compliance

# Exactly one primary cause per PF-failed instance
BUCKETS = (
    "policy_too_strict",
    "agent_not_adapting",
    "runner_integration_bug",
    "budget_regression",
    "stochasticity",
)

# Binaries that are local tooling; if denied and instance failed -> policy_too_strict
BENIGN_BINARIES = frozenset({"pip", "pytest", "make", "ruff", "nox", "tox", "coverage", "black", "mypy"})

# Network-only binaries; if denied -> agent should have adapted
NETWORK_BINARIES = frozenset({"curl", "wget", "ssh", "scp", "nc", "ncat", "telnet", "ftp", "ping", "nslookup", "dig"})


def load_json(path: Path) -> Optional[dict]:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def get_pf_failed_instances(baseline_eval_dir: Path, pf_eval_dir: Path) -> list[str]:
    """Instances that baseline resolved but PF did not."""
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


def get_harness_status_for_instance(eval_dir: Path, instance_id: str, run_id: str = "pf") -> Optional[str]:
    """Per-instance status from harness: patch_apply_failed, timeout, tests_fail, error."""
    # Harness writes run_id/model/instance_id/report.json or instance.log
    for base in (eval_dir, eval_dir / "evaluation_logs"):
        if not base.is_dir():
            continue
        run_part = base / run_id
        if not run_part.is_dir():
            continue
        for model_dir in run_part.iterdir():
            if not model_dir.is_dir():
                continue
            inst_dir = model_dir / instance_id
            report_path = inst_dir / "report.json"
            if report_path.exists():
                d = load_json(report_path)
                if d and instance_id in d:
                    rec = d[instance_id]
                    if not rec.get("patch_successfully_applied", True):
                        return "patch_apply_failed"
                    if rec.get("resolved"):
                        return "resolved"
                    return "tests_fail"
            log_path = inst_dir / "instance.log"
            if log_path.exists():
                try:
                    t = log_path.read_text(encoding="utf-8", errors="replace")
                    if "timed out" in t.lower() or "timeout" in t.lower() or "exceeded" in t.lower():
                        return "timeout"
                except OSError:
                    pass
    return None


def categorize_one(
    instance_id: str,
    baseline_eval_dir: Path,
    pf_eval_dir: Path,
    pf_run_dir: Optional[Path],
) -> tuple[str, dict]:
    """
    Assign exactly one primary cause. Returns (bucket, details).
    """
    harness_status = get_harness_status_for_instance(pf_eval_dir, instance_id)
    compliance = load_compliance(pf_run_dir, instance_id) if pf_run_dir and pf_run_dir.exists() else None
    violations = (compliance or {}).get("violations", 0) or 0
    reason_codes = (compliance or {}).get("reason_codes") or []

    # 1) Runner integration bug: patch didn't apply
    if harness_status == "patch_apply_failed":
        return "runner_integration_bug", {"harness_status": harness_status, "violations": violations}

    # 2) Budget regression: timeout
    if harness_status == "timeout":
        return "budget_regression", {"harness_status": harness_status}

    # 3) and 4) Use violation_details to see commands: benign tooling -> policy_too_strict; network -> agent_not_adapting
    if violations > 0:
        details = (compliance or {}).get("violation_details") or []
        payloads = [d.get("payload", {}) for d in details]
        cmd_snippets = [str(p.get("command_or_path", ""))[:300].lower() for p in payloads]
        has_network = any(
            any(n in c for n in ("curl", "wget", "ssh ", "scp ", "nc ", "nslookup", "dig ", "telnet", "ftp "))
            for c in cmd_snippets
        )
        has_benign = any(
            any(n in c for n in ("pip install -e", "pip install .", "python -m pytest", "pytest ", "make ", "ruff ", "nox ", "tox ", "coverage ", "black ", "mypy "))
            for c in cmd_snippets
        )
        if has_benign:
            return "policy_too_strict", {"violations": violations, "reason_codes": reason_codes}
        if has_network:
            return "agent_not_adapting", {"violations": violations, "reason_codes": reason_codes}
        if any(r in ("path_forbidden", "path_outside_workspace") for r in reason_codes):
            return "policy_too_strict", {"violations": violations, "reason_codes": reason_codes}
        return "policy_too_strict", {"violations": violations, "reason_codes": reason_codes}

    # 5) Stochasticity: no violations, no timeout, no patch apply fail
    return "stochasticity", {"harness_status": harness_status or "tests_fail", "violations": 0}


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Categorize PF failures into 5 buckets (one primary cause per instance).",
    )
    parser.add_argument(
        "--experiment-dir",
        type=str,
        default="runs/exp-step2-lite-smoke",
        help="Experiment dir containing baseline/eval and pf/eval",
    )
    parser.add_argument(
        "--baseline-eval-dir",
        type=str,
        default="",
        help="Override baseline eval dir",
    )
    parser.add_argument(
        "--pf-eval-dir",
        type=str,
        default="",
        help="Override PF eval dir",
    )
    parser.add_argument(
        "--pf-run-dir",
        type=str,
        required=True,
        help="PF run dir (runs/<run_id>) for policy_compliance_summary per instance",
    )
    parser.add_argument(
        "--out-json",
        type=str,
        default="",
        help="Output JSON path (default: <experiment-dir>/pf_failure_categories.json)",
    )
    parser.add_argument(
        "--out-csv",
        type=str,
        default="",
        help="Output CSV path (default: <experiment-dir>/pf_failure_categories.csv)",
    )
    args = parser.parse_args()

    exp_dir = Path(args.experiment_dir)
    baseline_eval = Path(args.baseline_eval_dir or str(exp_dir / "baseline" / "eval"))
    pf_eval = Path(args.pf_eval_dir or str(exp_dir / "pf" / "eval"))
    pf_run = Path(args.pf_run_dir)
    out_json = Path(args.out_json or str(exp_dir / "pf_failure_categories.json"))
    out_csv = Path(args.out_csv or str(exp_dir / "pf_failure_categories.csv"))

    pf_failed = get_pf_failed_instances(baseline_eval, pf_eval)
    if not pf_failed:
        print("No PF-failed instances (baseline resolved but PF did not).", file=sys.stderr)
        out_json.parent.mkdir(parents=True, exist_ok=True)
        report = {"pf_failed_count": 0, "instances": [], "bucket_counts": {b: 0 for b in BUCKETS}}
        out_json.write_text(json.dumps(report, indent=2), encoding="utf-8")
        with open(out_csv, "w", newline="", encoding="utf-8") as f:
            f.write("instance_id,primary_cause,details\n")
        print(f"Wrote {out_json}, {out_csv}")
        return 0

    results = []
    bucket_counts = {b: 0 for b in BUCKETS}
    for iid in pf_failed:
        bucket, details = categorize_one(iid, baseline_eval, pf_eval, pf_run)
        results.append({"instance_id": iid, "primary_cause": bucket, "details": details})
        bucket_counts[bucket] = bucket_counts.get(bucket, 0) + 1

    report = {
        "pf_failed_count": len(pf_failed),
        "instances": results,
        "bucket_counts": bucket_counts,
    }
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(report, indent=2), encoding="utf-8")

    import csv
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["instance_id", "primary_cause", "details"])
        w.writeheader()
        for r in results:
            w.writerow({"instance_id": r["instance_id"], "primary_cause": r["primary_cause"], "details": json.dumps(r["details"])})

    print(f"PF-failed instances: {len(pf_failed)}")
    for b in BUCKETS:
        print(f"  {b}: {bucket_counts[b]}")
    print(f"Wrote {out_json}, {out_csv}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
