# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Contract test for summarize_stress_run.py: synthetic run dirs + compare.json -> stress_summary.json.

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_summarize_stress_run_produces_valid_summary_with_timing():
    """With synthetic runpair and compare.json, summarize_stress_run produces stress_summary.json with required keys."""
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b", "c"],
        n_resolved_baseline=2,
        n_resolved_pf=1,
        n_applies_false=0,
    )
    try:
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        compare_path = root / "compare.json"
        compare_path.write_text(
            json.dumps({
                "baseline": {"solve_rate": 2 / 3},
                "pf": {"solve_rate": 1 / 3},
                "patch_apply": {"total": 6, "applies_true": 6, "applies_false": 0},
                "empty_patch_reasons_topN": [],
            }, indent=2),
            encoding="utf-8",
        )
        out_path = root / "stress_summary.json"
        r = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "experiments" / "scripts" / "summarize_stress_run.py"),
                "--baseline-run-dir", str(baseline_run),
                "--pf-run-dir", str(pf_run),
                "--compare-json", str(compare_path),
                "--out", str(out_path),
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert r.returncode == 0, (r.stdout, r.stderr)
        assert out_path.exists()
        data = json.loads(out_path.read_text(encoding="utf-8"))
        assert "timeout_rate_baseline" in data
        assert "timeout_rate_pf" in data
        assert "wall_clock_s_median_baseline" in data
        assert "wall_clock_s_median_pf" in data
        assert "guard_overhead_s_median" in data
        assert "baseline_solve_rate" in data
        assert "pf_solve_rate" in data
        assert "patch_apply_applies_false" in data
        assert data["patch_apply_applies_false"] == 0
        assert data["baseline_solve_rate"] == pytest.approx(2 / 3)
        assert data["pf_solve_rate"] == pytest.approx(1 / 3)
        # No timing.json in fixture -> fallback cost_report; wall_clock 1.5 -> median 1.5
        assert data["wall_clock_s_median_baseline"] == 1.5
        assert data["wall_clock_s_median_pf"] == 1.5
        assert data["tokens_median_baseline"] == 30.0
        assert data["tokens_median_pf"] == 30.0
        assert data["tool_calls_median_baseline"] == 2.0
        assert data["tool_calls_median_pf"] == 2.0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_summarize_stress_run_timeout_rate_from_timing_json():
    """When timing.json has timeout_reached=true, stress summary reflects timeout rate."""
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["i1", "i2"],
        n_resolved_baseline=2,
        n_resolved_pf=1,
        n_applies_false=0,
    )
    try:
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        # Add timing.json with one timeout for PF
        (pf_run / "i1" / "timing.json").write_text(
            json.dumps({
                "wall_clock_s": 300.0,
                "tool_calls": 25,
                "max_steps_reached": True,
                "timeout_reached": True,
                "termination_reason": "timeout",
            }, indent=2),
            encoding="utf-8",
        )
        (pf_run / "i2" / "timing.json").write_text(
            json.dumps({
                "wall_clock_s": 60.0,
                "tool_calls": 5,
                "max_steps_reached": False,
                "timeout_reached": False,
                "termination_reason": "success",
            }, indent=2),
            encoding="utf-8",
        )
        compare_path = root / "compare.json"
        compare_path.write_text(
            json.dumps({
                "baseline": {"solve_rate": 1.0},
                "pf": {"solve_rate": 0.5},
                "patch_apply": {"total": 4, "applies_true": 4, "applies_false": 0},
                "empty_patch_reasons_topN": [],
            }, indent=2),
            encoding="utf-8",
        )
        out_path = root / "stress_summary.json"
        r = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "experiments" / "scripts" / "summarize_stress_run.py"),
                "--baseline-run-dir", str(baseline_run),
                "--pf-run-dir", str(pf_run),
                "--compare-json", str(compare_path),
                "--out", str(out_path),
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert r.returncode == 0, (r.stdout, r.stderr)
        data = json.loads(out_path.read_text(encoding="utf-8"))
        assert data["timeout_rate_pf"] == pytest.approx(0.5)  # 1 of 2
        assert data["wall_clock_s_median_pf"] == 180.0  # median(300, 60)
        assert data["tokens_median_pf"] == 30.0
    finally:
        shutil.rmtree(root, ignore_errors=True)
