#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# From compare.csv, list instance IDs by delta category: baseline-solved/PF-failed,
# PF-solved/baseline-failed, both solved, and PF violations on solved instances.
#
# Immediately actionable outputs:
#   baseline_solved_pf_failed.txt  - The list that matters for solve-parity (baseline solved, PF did not).
#   pf_violations_on_solved.txt   - PF "solved" but policy flagged violations; verify these are legitimate, not false positives.

import argparse
import csv
from pathlib import Path


def _pick_col(cols, candidates):
    low = {c.lower(): c for c in cols}
    for cand in candidates:
        if cand.lower() in low:
            return low[cand.lower()]
    return None


def _truthy(v):
    if v is None:
        return False
    s = str(v).strip().lower()
    return s in ("1", "true", "yes", "y", "pass", "resolved", "success")


def main():
    ap = argparse.ArgumentParser(
        description="List instance IDs by delta category from compare.csv (baseline vs PF resolved/failed).",
    )
    ap.add_argument("--compare-csv", required=True, help="Path to compare.csv from compare_runs.py")
    ap.add_argument("--out-dir", required=True, help="Directory to write .txt lists (one instance_id per line)")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    with open(args.compare_csv, newline="", encoding="utf-8") as f:
        rows = list(csv.DictReader(f))

    if not rows:
        raise SystemExit("compare.csv has no rows")

    cols = rows[0].keys()
    col_id = _pick_col(cols, ["instance_id", "id"])
    col_b = _pick_col(cols, ["baseline_resolved", "baseline_pass", "baseline_status", "baseline_solved"])
    col_p = _pick_col(cols, ["pf_resolved", "pf_pass", "pf_status", "pf_solved"])
    col_v = _pick_col(cols, ["pf_violations", "violations", "pf_violation_count"])

    if not col_id or not col_b or not col_p:
        raise SystemExit(f"Missing required columns. Found: {list(cols)}")

    baseline_solved_pf_failed = []
    pf_solved_baseline_failed = []
    both_solved = []
    pf_violations_on_solved = []

    for r in rows:
        iid = r.get(col_id, "").strip()
        if not iid or iid == "_summary":
            continue
        b_ok = _truthy(r.get(col_b))
        p_ok = _truthy(r.get(col_p))
        v = r.get(col_v) if col_v else None
        v_n = int(v) if (v is not None and str(v).strip().isdigit()) else 0

        if b_ok and not p_ok:
            baseline_solved_pf_failed.append(iid)
        if p_ok and not b_ok:
            pf_solved_baseline_failed.append(iid)
        if b_ok and p_ok:
            both_solved.append(iid)
            if v_n > 0:
                pf_violations_on_solved.append(iid)

    def write_list(name, items):
        p = out_dir / name
        p.write_text("\n".join(items) + ("\n" if items else ""), encoding="utf-8")
        print(f"Wrote {p} ({len(items)})")

    write_list("baseline_solved_pf_failed.txt", baseline_solved_pf_failed)
    write_list("pf_solved_baseline_failed.txt", pf_solved_baseline_failed)
    write_list("both_solved.txt", both_solved)
    write_list("pf_violations_on_solved.txt", pf_violations_on_solved)


if __name__ == "__main__":
    main()
