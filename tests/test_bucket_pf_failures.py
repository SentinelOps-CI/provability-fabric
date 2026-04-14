# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Output-shape contract tests for bucket_pf_failures_from_cases.py: given synthetic compare.csv and cases dir, produces valid CSV.

from __future__ import annotations

import csv
import json
import sys
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def test_bucket_pf_failures_produces_valid_csv_with_expected_columns(tmp_path):
    """Given synthetic compare.csv and cases dir, bucket_pf_failures_from_cases produces CSV with instance_id, bucket, etc."""
    compare_csv = tmp_path / "compare.csv"
    with open(compare_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["instance_id", "baseline_resolved", "pf_resolved", "pf_status", "baseline_status"])
        w.writeheader()
        w.writerow({"instance_id": "inst1", "baseline_resolved": "0", "pf_resolved": "0", "pf_status": "timeout", "baseline_status": "resolved"})
    cases_dir = tmp_path / "cases"
    cases_dir.mkdir()
    inst1 = cases_dir / "inst1"
    inst1.mkdir()
    (inst1 / "pf").mkdir()
    (inst1 / "pf" / "policy_compliance_summary.json").write_text(
        json.dumps({"violations": 2, "reason_codes": ["binary_forbidden", "network_denied"]}), encoding="utf-8"
    )
    (inst1 / "pf" / "model.patch").write_text("diff --git a/x b/x\n", encoding="utf-8")
    out_csv = tmp_path / "buckets.csv"
    import subprocess
    r = subprocess.run(
        [sys.executable, str(REPO_ROOT / "experiments" / "scripts" / "bucket_pf_failures_from_cases.py"),
         "--compare-csv", str(compare_csv), "--cases-dir", str(cases_dir), "--out-csv", str(out_csv)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, (r.stdout, r.stderr)
    assert out_csv.exists()
    with open(out_csv, newline="", encoding="utf-8") as f:
        reader = csv.DictReader(f)
        rows = list(reader)
    assert len(rows) == 1
    row = rows[0]
    assert "instance_id" in row
    assert "bucket" in row
    assert "pf_status" in row
    assert "baseline_status" in row
    assert "violations" in row
    assert "reason_codes" in row
    assert "notes" in row
    assert row["instance_id"] == "inst1"
    assert row["bucket"] == "policy_denial_or_violation"
