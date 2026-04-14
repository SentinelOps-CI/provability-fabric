# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.cost_reporter import CostReporter


def test_cost_reporter_aggregate_token_totals():
    reports = [
        {"instance_id": "a", "prompt_tokens": 10, "completion_tokens": 5},
        {"instance_id": "b", "prompt_tokens": 3, "completion_tokens": 7},
    ]
    assert CostReporter.aggregate_token_totals(reports) == {
        "prompt_tokens_total": 13,
        "completion_tokens_total": 12,
    }


def test_cost_reporter_build_and_write(tmp_path: Path):
    built = []

    def _build(**kwargs):
        built.append(kwargs)
        return {"instance_id": kwargs["instance_id"], "x": 1}

    written = []

    def _write(inst_dir, rec):
        written.append((inst_dir, rec))

    cr = CostReporter(_build, _write)
    r = cr.build_report(instance_id="i1", model_name="m")
    assert r["instance_id"] == "i1"
    cr.write_report(tmp_path / "inst", r)
    assert len(written) == 1
