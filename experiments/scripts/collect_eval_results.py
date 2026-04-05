#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Collect SWE-bench harness results: pass/fail per instance and failure reason buckets
# (patch didn't apply, tests fail, timeout, empty patch, other error).
# Reads run report JSON and optionally per-instance report.json / instance.log.

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

# Ensure repo root on path
_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from experiments.harness_report import (
    EMPTY_PATCH_IDS,
    ERROR_IDS,
    RESOLVED_IDS,
    TOTAL_INSTANCES,
    UNRESOLVED_IDS,
    find_run_report,
    load_run_report,
)


def find_instance_report(log_base: Path, run_id: str, model_name: str, instance_id: str) -> Path | None:
    """Find per-instance report.json under log_base/run_id/model/instance_id or evaluation_logs/..."""
    for base in (log_base, log_base / "evaluation_logs"):
        report_path = base / run_id / model_name.replace("/", "__") / instance_id / "report.json"
        if report_path.exists():
            return report_path
    return None


def find_instance_log(log_base: Path, run_id: str, model_name: str, instance_id: str) -> Path | None:
    """Find per-instance instance.log (LOG_INSTANCE)."""
    for base in (log_base, log_base / "evaluation_logs"):
        log_path = base / run_id / model_name.replace("/", "__") / instance_id / "instance.log"
        if log_path.exists():
            return log_path
    return None


def classify_error(
    instance_id: str,
    eval_dir: Path,
    run_id: str,
    model_name: str,
) -> str:
    """Classify an error instance: patch_apply_failed, timeout, empty_patch, or error."""
    report_path = find_instance_report(eval_dir, run_id, model_name, instance_id)
    if report_path:
        try:
            data = json.loads(report_path.read_text(encoding="utf-8"))
            inst = data.get(instance_id, {})
            if inst.get("patch_is_None") or not inst.get("patch_exists"):
                return "empty_patch"
            if not inst.get("patch_successfully_applied", True):
                return "patch_apply_failed"
        except (json.JSONDecodeError, OSError, KeyError):
            pass
    log_path = find_instance_log(eval_dir, run_id, model_name, instance_id)
    if log_path:
        try:
            content = log_path.read_text(encoding="utf-8", errors="replace")
            if "timed out" in content.lower() or "timeout" in content.lower() or "exceeded" in content.lower():
                return "timeout"
            if "apply patch fail" in content.lower() or "apply_patch_fail" in content.lower():
                return "patch_apply_failed"
        except OSError:
            pass
    return "error"


def collect_one(eval_dir: Path, run_label: str, model_name: str | None) -> dict[str, Any]:
    """
    Collect pass/fail and failure buckets for one eval dir.
    Returns dict with: run_label, total, resolved, unresolved, error, empty_patch,
    per_instance (list of {instance_id, status}), failure_buckets (counts).
    """
    eval_dir = Path(eval_dir)
    report_path = find_run_report(eval_dir)
    if not report_path:
        return {
            "run_label": run_label,
            "error": f"No run report found in {eval_dir}",
            "total": 0,
            "resolved": 0,
            "unresolved": 0,
            "error": 0,
            "empty_patch": 0,
            "per_instance": [],
            "failure_buckets": {},
        }
    data = load_run_report(report_path)
    if not data:
        return {
            "run_label": run_label,
            "error": f"Invalid run report: {report_path}",
            "total": 0,
            "per_instance": [],
            "failure_buckets": {},
        }

    resolved_ids = set(data.get(RESOLVED_IDS, []))
    unresolved_ids = set(data.get(UNRESOLVED_IDS, []))
    error_ids = set(data.get(ERROR_IDS, []))
    empty_patch_ids = set(data.get(EMPTY_PATCH_IDS, []))

    total = data.get(TOTAL_INSTANCES, len(resolved_ids) + len(unresolved_ids) + len(error_ids) + len(empty_patch_ids))
    # Harness writes report as {model_name}.{run_id}.json (e.g. pf-swebench-openhands.baseline.json)
    stem = report_path.stem
    if not model_name and "." in stem:
        parts = stem.rsplit(".", 1)
        model_name = parts[0] if len(parts) == 2 else "pf-swebench-openhands"
        run_id = parts[1] if len(parts) == 2 else ("baseline" if "baseline" in run_label.lower() else "pf")
    else:
        model_name = model_name or "pf-swebench-openhands"
        run_id = "baseline" if "baseline" in run_label.lower() else "pf"
    buckets: dict[str, int] = {
        "resolved": len(resolved_ids),
        "tests_fail": len(unresolved_ids),
        "empty_patch": len(empty_patch_ids),
        "patch_apply_failed": 0,
        "timeout": 0,
        "error": 0,
    }
    error_classifications: dict[str, str] = {}
    for iid in error_ids:
        kind = classify_error(iid, eval_dir, run_id, model_name)
        error_classifications[iid] = kind
        if kind in buckets:
            buckets[kind] += 1
        else:
            buckets["error"] += 1

    per_instance: list[dict[str, str]] = []
    all_ids = resolved_ids | unresolved_ids | error_ids | empty_patch_ids
    for iid in sorted(all_ids):
        if iid in resolved_ids:
            status = "pass"
        elif iid in unresolved_ids:
            status = "tests_fail"
        elif iid in empty_patch_ids:
            status = "empty_patch"
        else:
            status = error_classifications.get(iid, "error")
        per_instance.append({"instance_id": iid, "status": status})

    return {
        "run_label": run_label,
        "total": total,
        "resolved": len(resolved_ids),
        "unresolved": len(unresolved_ids),
        "error": len(error_ids),
        "empty_patch": len(empty_patch_ids),
        "per_instance": per_instance,
        "failure_buckets": buckets,
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Collect SWE-bench harness results: pass/fail per instance and failure reason buckets.",
    )
    parser.add_argument(
        "eval_dirs",
        nargs="+",
        type=str,
        help="One or two eval output dirs (e.g. runs/.../baseline/eval runs/.../pf/eval)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output full summary as JSON to stdout",
    )
    parser.add_argument(
        "--csv",
        type=str,
        default="",
        help="Write per-instance pass/fail to this CSV (instance_id, run_label, status)",
    )
    args = parser.parse_args()

    if len(args.eval_dirs) == 0:
        print("Provide at least one eval dir.", file=sys.stderr)
        return 2

    labels = ["baseline", "pf"] if len(args.eval_dirs) == 2 else [f"run_{i}" for i in range(len(args.eval_dirs))]
    results = []
    for eval_dir, label in zip(args.eval_dirs, labels):
        r = collect_one(Path(eval_dir), label, None)
        results.append(r)

    if args.json:
        print(json.dumps({"runs": results}, indent=2))
    else:
        for r in results:
            if "error" in r and r["error"] and isinstance(r["error"], str):
                print(f"{r['run_label']}: {r['error']}")
                continue
            print(f"\n{r['run_label']}")
            print(f"  total: {r.get('total', 0)}")
            print(f"  pass (resolved): {r.get('resolved', 0)}")
            print(f"  failure buckets: {r.get('failure_buckets', {})}")
            for row in (r.get("per_instance") or [])[:20]:
                print(f"    {row['instance_id']}: {row['status']}")
            if len(r.get("per_instance") or []) > 20:
                print(f"    ... and {len(r['per_instance']) - 20} more")

    if args.csv:
        import csv
        csv_path = Path(args.csv)
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        with open(csv_path, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(["instance_id", "run_label", "status"])
            for r in results:
                for row in r.get("per_instance") or []:
                    w.writerow([row["instance_id"], r["run_label"], row["status"]])
        print(f"\nWrote per-instance CSV: {csv_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
