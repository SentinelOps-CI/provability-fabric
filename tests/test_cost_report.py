# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Unit tests for cost_report: build_cost_report, write_cost_report, write_summary; load_summary with missing files.

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.cost_report import (
    build_cost_report,
    write_cost_report,
    write_summary,
    SUMMARY_CSV_FILENAME,
    SUMMARY_JSON_FILENAME,
)
from experiments.run_evidence import load_summary, load_cost_report
from bench.swebench.util import sanitize_instance_id


def test_build_cost_report():
    r = build_cost_report(
        instance_id="django__django-123",
        model_name="gpt-4o",
        prompt_tokens=100,
        completion_tokens=50,
        iterations=3,
        tool_calls=10,
        wall_clock_s=12.5,
        run_id="run-1",
        guarded=True,
    )
    assert r["instance_id"] == "django__django-123"
    assert r["run_id"] == "run-1"
    assert r["guarded"] is True
    assert r["prompt_tokens"] == 100
    assert r["wall_clock_s"] == 12.5


def test_write_cost_report_and_write_summary():
    with tempfile.TemporaryDirectory() as td:
        run_dir = Path(td)
        reports = [
            build_cost_report("inst-a", "m", run_id="r1", guarded=False),
            build_cost_report("inst-b", "m", run_id="r1", guarded=False),
        ]
        write_summary(run_dir, reports, "r1", False)
        assert (run_dir / SUMMARY_JSON_FILENAME).exists()
        summary = json.loads((run_dir / SUMMARY_JSON_FILENAME).read_text(encoding="utf-8"))
        assert summary["run_id"] == "r1"
        assert summary["n_instances"] == 2
        assert len(summary["instances"]) == 2
        assert (run_dir / SUMMARY_CSV_FILENAME).exists()


def test_write_summary_subset_missing_cost_files_aggregation_stable():
    with tempfile.TemporaryDirectory() as td:
        run_dir = Path(td)
        reports = [
            build_cost_report("inst-a", "m", run_id="r1", guarded=True),
            build_cost_report("inst-b", "m", run_id="r1", guarded=True),
        ]
        write_summary(run_dir, reports, "r1", True)
        inst_a_dir = run_dir / sanitize_instance_id("inst-a")
        inst_a_dir.mkdir(parents=True, exist_ok=True)
        write_cost_report(inst_a_dir, reports[0])
        s = load_summary(run_dir)
        assert s is not None
        assert len(s["instances"]) == 2
        cr = load_cost_report(run_dir, "inst-a")
        assert cr is not None
        cr_missing = load_cost_report(run_dir, "inst-b")
        assert cr_missing is None
