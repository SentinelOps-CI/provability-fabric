# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Unit tests for compare_runs aggregate and gate flags (synthetic fixtures only).

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import json

from experiments.scripts.compare_runs import aggregate
from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_aggregate_solve_rates_and_patch_apply():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b", "c"],
        n_resolved_baseline=2,
        n_resolved_pf=1,
        n_applies_false=0,
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        report = aggregate(baseline_eval, pf_eval, baseline_run, pf_run)
        assert report["baseline"]["solve_rate"] is not None
        assert report["pf"]["solve_rate"] is not None
        assert isinstance(report["baseline"]["solve_rate"], (int, float))
        assert isinstance(report["pf"]["solve_rate"], (int, float))
        pa = report.get("patch_apply") or {}
        assert pa.get("total") == 6
        assert pa.get("applies_false") == 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_aggregate_applies_false_count():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b", "c"],
        n_resolved_baseline=2,
        n_resolved_pf=1,
        n_applies_false=2,
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        report = aggregate(baseline_eval, pf_eval, baseline_run, pf_run)
        pa = report.get("patch_apply") or {}
        assert pa.get("applies_false") == 4
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_require_harness_fails_when_eval_missing():
    root = make_fake_runpair(run_id="r1", instance_ids=["a"], n_resolved_baseline=1, n_resolved_pf=1)
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        for f in pf_eval.iterdir():
            f.unlink()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir", str(exp_dir),
                "--baseline-eval-dir", str(baseline_eval),
                "--pf-eval-dir", str(pf_eval),
                "--baseline-run-dir", str(baseline_run),
                "--pf-run-dir", str(pf_run),
                "--require-harness",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_require_patch_apply_fails_when_applies_false():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b"],
        n_resolved_baseline=1,
        n_resolved_pf=1,
        n_applies_false=1,
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir", str(exp_dir),
                "--baseline-eval-dir", str(baseline_eval),
                "--pf-eval-dir", str(pf_eval),
                "--baseline-run-dir", str(baseline_run),
                "--pf-run-dir", str(pf_run),
                "--require-harness",
                "--require-patch-apply",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_aggregate_includes_per_attempt_metrics_and_estimated_usd():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["x", "y"],
        n_resolved_baseline=0,
        n_resolved_pf=0,
        n_applies_false=0,
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        report = aggregate(baseline_eval, pf_eval, baseline_run, pf_run)
        assert "harness_eval" in report
        assert report["harness_eval"]["baseline"]["n_parsed"] == 0
        assert report["baseline"]["cost_per_solved"] is None
        bcpa = report["baseline"]["cost_per_attempt"]
        assert bcpa["n"] == 2
        assert bcpa["prompt_tokens"] == 10.0
        assert report["baseline"]["latency_per_attempt"]["n"] == 2
        assert report["baseline"]["termination_mix"]["n_with_timing"] == 0
        assert report["estimated_cost_usd"]["pricing_version"]
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_require_compliance_fails_when_pf_missing_summary():
    root = make_fake_runpair(run_id="r1", instance_ids=["a"], n_resolved_baseline=1, n_resolved_pf=1)
    try:
        pf_inst = root / "pf" / "r1" / "a"
        if not pf_inst.exists():
            pf_inst = next((root / "pf" / "r1").iterdir())
        comp = pf_inst / "policy_compliance_summary.json"
        if comp.exists():
            comp.unlink()
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir",
                str(exp_dir),
                "--baseline-eval-dir",
                str(baseline_eval),
                "--pf-eval-dir",
                str(pf_eval),
                "--baseline-run-dir",
                str(baseline_run),
                "--pf-run-dir",
                str(pf_run),
                "--require-compliance",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
        assert "require-compliance" in (proc.stderr or "").lower() or "missing" in (proc.stderr or "").lower()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_require_priced_models_fails_on_unknown_model():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a"],
        n_resolved_baseline=1,
        n_resolved_pf=1,
        summary_model_name="unknown-model-not-in-pricing-table-xyz",
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir",
                str(exp_dir),
                "--baseline-eval-dir",
                str(baseline_eval),
                "--pf-eval-dir",
                str(pf_eval),
                "--baseline-run-dir",
                str(baseline_run),
                "--pf-run-dir",
                str(pf_run),
                "--require-priced-models",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
        assert "require-priced-models" in (proc.stderr or "").lower() or "model_pricing" in (proc.stderr or "").lower()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_require_harness_fails_on_eval_run_id_mismatch():
    root = make_fake_runpair(run_id="r1", instance_ids=["a"], n_resolved_baseline=1, n_resolved_pf=1)
    try:
        meta = root / "baseline" / "eval" / "eval_metadata.json"
        meta.write_text('{"run_id": "other-run"}\n', encoding="utf-8")
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir",
                str(exp_dir),
                "--baseline-eval-dir",
                str(baseline_eval),
                "--pf-eval-dir",
                str(pf_eval),
                "--baseline-run-dir",
                str(baseline_run),
                "--pf-run-dir",
                str(pf_run),
                "--require-harness",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
        assert "mismatch" in (proc.stderr or "").lower()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_all_strict_flags_pass_on_healthy_fixture():
    """Golden path: full strict gate set succeeds on synthetic runpair."""
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b"],
        n_resolved_baseline=2,
        n_resolved_pf=2,
        n_applies_false=0,
    )
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        exp_dir = root / "exp"
        exp_dir.mkdir()
        script = REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--experiment-dir",
                str(exp_dir),
                "--baseline-eval-dir",
                str(baseline_eval),
                "--pf-eval-dir",
                str(pf_eval),
                "--baseline-run-dir",
                str(baseline_run),
                "--pf-run-dir",
                str(pf_run),
                "--require-harness",
                "--require-compliance",
                "--require-patch-apply",
                "--require-priced-models",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0, (proc.stdout or "") + "\n" + (proc.stderr or "")
        assert (exp_dir / "compare.json").is_file()
        assert (exp_dir / "compare.csv").is_file()
        assert (exp_dir / "metrics_full.json").is_file()
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_report_valid_against_schema():
    root = make_fake_runpair(run_id="r1", instance_ids=["a", "b"], n_resolved_baseline=1, n_resolved_pf=1)
    try:
        baseline_eval = root / "baseline" / "eval"
        pf_eval = root / "pf" / "eval"
        baseline_run = root / "baseline" / "r1"
        pf_run = root / "pf" / "r1"
        report = aggregate(baseline_eval, pf_eval, baseline_run, pf_run)
        schema_path = REPO_ROOT / "experiments" / "schemas" / "compare_report.schema.json"
        assert schema_path.exists()
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        try:
            import jsonschema
            jsonschema.validate(report, schema)
        except ImportError:
            pass
        else:
            assert "baseline" in report
            assert "patch_apply" in report
            assert "violation_reasons_top10" in report
    finally:
        shutil.rmtree(root, ignore_errors=True)
