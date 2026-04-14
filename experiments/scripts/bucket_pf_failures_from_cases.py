#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Automatic bucketing (policy vs budget vs patch-format vs agent quality) from
# compare.csv and extracted case bundles (from extract_case_bundle.py). Outputs
# one row per instance with bucket and notes. For harness-based categorization
# with policy_too_strict / agent_not_adapting etc., use categorize_pf_failures.py.

import argparse
import csv
import json
from pathlib import Path


def read_json(p: Path) -> dict | None:
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Bucket PF failures from compare.csv and case bundles (policy vs budget vs patch-format vs agent quality).",
    )
    ap.add_argument("--compare-csv", required=True, help="Path to compare.csv from compare_runs.py")
    ap.add_argument("--cases-dir", required=True, help="Cases root (e.g. analysis/cases from extract_case_bundle.py)")
    ap.add_argument("--out-csv", required=True, help="Output CSV path")
    args = ap.parse_args()

    compare_rows: dict[str, dict[str, str]] = {}
    with open(args.compare_csv, newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            iid = row.get("instance_id") or row.get("id")
            if iid and iid != "_summary":
                compare_rows[iid] = row

    out: list[dict[str, str | int]] = []
    cases_dir = Path(args.cases_dir)
    if not cases_dir.is_dir():
        raise SystemExit(f"Cases dir not found or not a directory: {cases_dir}")

    for case_dir in sorted(cases_dir.iterdir()):
        if not case_dir.is_dir():
            continue
        iid = case_dir.name
        row = compare_rows.get(iid, {})

        pf_sum = read_json(case_dir / "pf" / "policy_compliance_summary.json") or {}
        violations = int(pf_sum.get("violations", pf_sum.get("total_violations", 0)) or 0)
        reason_codes = pf_sum.get("reason_codes", []) or []
        if not isinstance(reason_codes, list):
            reason_codes = [str(reason_codes)]

        pf_patch = case_dir / "pf" / "model.patch"
        patch_empty = (not pf_patch.exists()) or (pf_patch.read_text(encoding="utf-8").strip() == "")

        pf_status = (row.get("pf_status") or row.get("pf_result") or row.get("pf_outcome") or "").lower()
        base_status = (row.get("baseline_status") or row.get("baseline_result") or row.get("baseline_outcome") or "").lower()

        bucket = "unknown"
        notes: list[str] = []

        if violations > 0:
            bucket = "policy_denial_or_violation"
            notes.append(f"violations={violations}")
            notes.append(f"reason_codes={','.join(reason_codes) if reason_codes else '[]'}")
        elif patch_empty:
            bucket = "empty_patch_or_patch_write_failed"
        elif "timeout" in pf_status:
            bucket = "budget_timeout"
        elif "patch_apply" in pf_status or "apply_failed" in pf_status:
            bucket = "patch_format_or_apply"
        elif "tests_fail" in pf_status or "fail" in pf_status:
            bucket = "agent_quality_or_missing_tooling"
        else:
            bucket = "needs_manual_read"

        out.append({
            "instance_id": iid,
            "bucket": bucket,
            "pf_status": pf_status,
            "baseline_status": base_status,
            "violations": violations,
            "reason_codes": "|".join(reason_codes),
            "notes": ";".join(notes),
        })

    fieldnames = ["instance_id", "bucket", "pf_status", "baseline_status", "violations", "reason_codes", "notes"]
    Path(args.out_csv).parent.mkdir(parents=True, exist_ok=True)
    with open(args.out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(out)

    print(f"Wrote {args.out_csv} ({len(out)} rows)")


if __name__ == "__main__":
    main()
