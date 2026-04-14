# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.summary_writer import SummaryWriter


def test_summary_writer_with_write_summary_fn():
    written = []

    def fake_write_summary(run_dir, reports, run_id, guarded):
        written.append((run_dir, len(reports), run_id, guarded))

    with tempfile.TemporaryDirectory() as tmp:
        rd = Path(tmp)
        reports = [{"instance_id": "a", "run_id": "r1", "guarded": False}]
        SummaryWriter(fake_write_summary).write_run_summary(
            rd,
            reports,
            "r1",
            False,
            instance_ids_planned=["a"],
            effective_model_name="m",
        )
        assert len(written) == 1
        assert written[0][1] == 1


def test_summary_writer_fallback_dict():
    d = SummaryWriter.build_fallback_summary_dict("r", True, ["a", "b"], "gpt-4o")
    assert d["n_instances"] == 2
    assert d["instances"][0]["instance_id"] == "a"


def test_summary_writer_fallback_without_cost_report_module():
    with tempfile.TemporaryDirectory() as tmp:
        rd = Path(tmp)
        SummaryWriter(write_summary_fn=None).write_run_summary(
            rd,
            [],
            "runx",
            False,
            instance_ids_planned=["i1"],
            effective_model_name="",
        )
        summary = json.loads((rd / "summary.json").read_text(encoding="utf-8"))
        assert summary["n_instances"] == 1
        assert summary["instances"][0]["instance_id"] == "i1"
