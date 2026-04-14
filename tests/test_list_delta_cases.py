# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Output-shape contract tests for list_delta_cases.py: given synthetic compare.csv, produces expected .txt files.

from __future__ import annotations

import csv
import sys
import tempfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def test_list_delta_cases_produces_expected_files(tmp_path):
    """Given a synthetic compare.csv, list_delta_cases produces baseline_solved_pf_failed.txt etc. with expected content."""
    compare_csv = tmp_path / "compare.csv"
    rows = [
        {"instance_id": "a", "baseline_resolved": "1", "pf_resolved": "0", "pf_violations": "0"},
        {"instance_id": "b", "baseline_resolved": "0", "pf_resolved": "1", "pf_violations": "0"},
        {"instance_id": "c", "baseline_resolved": "1", "pf_resolved": "1", "pf_violations": "0"},
    ]
    with open(compare_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=["instance_id", "baseline_resolved", "pf_resolved", "pf_violations"])
        w.writeheader()
        w.writerows(rows)
    out_dir = tmp_path / "out"
    out_dir.mkdir()
    import subprocess
    r = subprocess.run(
        [sys.executable, str(REPO_ROOT / "experiments" / "scripts" / "list_delta_cases.py"),
         "--compare-csv", str(compare_csv), "--out-dir", str(out_dir)],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
    )
    assert r.returncode == 0, (r.stdout, r.stderr)
    assert (out_dir / "baseline_solved_pf_failed.txt").exists()
    assert (out_dir / "pf_solved_baseline_failed.txt").exists()
    assert (out_dir / "both_solved.txt").exists()
    assert (out_dir / "pf_violations_on_solved.txt").exists()
    bspf = (out_dir / "baseline_solved_pf_failed.txt").read_text(encoding="utf-8").strip().splitlines()
    assert bspf == ["a"]
    psbf = (out_dir / "pf_solved_baseline_failed.txt").read_text(encoding="utf-8").strip().splitlines()
    assert psbf == ["b"]
    both = (out_dir / "both_solved.txt").read_text(encoding="utf-8").strip().splitlines()
    assert both == ["c"]
