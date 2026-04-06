# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_run_health_snapshot_json_counts():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["x", "y"],
        n_resolved_baseline=1,
        n_resolved_pf=1,
        n_applies_false=1,
    )
    try:
        run_dir = root / "baseline" / "r1"
        proc = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "experiments" / "scripts" / "run_health_snapshot.py"),
                "--run-dir",
                str(run_dir),
                "--json",
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0, proc.stderr
        out = json.loads(proc.stdout)
        assert out["patch_apply"]["total"] == 2
        assert out["patch_apply"]["applies_true"] == 1
        assert out["patch_apply"]["applies_false"] == 1
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_compare_runs_writes_meta_block():
    root = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b"],
        n_resolved_baseline=2,
        n_resolved_pf=2,
        n_applies_false=0,
    )
    try:
        exp_dir = root / "exp"
        exp_dir.mkdir()
        proc = subprocess.run(
            [
                sys.executable,
                str(REPO_ROOT / "experiments" / "scripts" / "compare_runs.py"),
                "--experiment-dir",
                str(exp_dir),
                "--baseline-eval-dir",
                str(root / "baseline" / "eval"),
                "--pf-eval-dir",
                str(root / "pf" / "eval"),
                "--baseline-run-dir",
                str(root / "baseline" / "r1"),
                "--pf-run-dir",
                str(root / "pf" / "r1"),
            ],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0, proc.stderr
        data = json.loads((exp_dir / "compare.json").read_text(encoding="utf-8"))
        assert "meta" in data
        assert data["meta"].get("compare_report_schema_version") == "1.1"
        assert data["meta"].get("generated_at")
        br = data["meta"].get("baseline_run_dir") or ""
        assert "baseline" in br and "r1" in br
    finally:
        shutil.rmtree(root, ignore_errors=True)
