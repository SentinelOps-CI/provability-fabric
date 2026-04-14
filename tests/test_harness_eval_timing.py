# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import os
import shutil
import sys
import time
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from experiments.scripts.harness_eval_timing import (
    collect_harness_seconds_per_instance,
    summarize_harness_eval_from_eval_dir,
)


def _write_log(base: Path, run: str, model: str, iid: str, seconds: float) -> None:
    d = base / "logs" / "run_evaluation" / run / model / iid
    d.mkdir(parents=True)
    (d / "run_instance.log").write_text(
        "header\nTest runtime: %.2f seconds\nfooter" % seconds,
        encoding="utf-8",
    )


def test_collect_harness_seconds_newest_run_wins(tmp_path: Path):
    ev = tmp_path / "eval"
    _write_log(ev, "run_old", "m", "i1", 10.0)
    _write_log(ev, "run_new", "m", "i1", 200.0)
    old_dir = ev / "logs" / "run_evaluation" / "run_old"
    new_dir = ev / "logs" / "run_evaluation" / "run_new"
    os.utime(old_dir, (1, 1))
    os.utime(new_dir, (time.time(), time.time()))
    per = collect_harness_seconds_per_instance(ev)
    assert per["i1"] == 200.0


def test_summarize_harness_eval_median_p95(tmp_path: Path):
    ev = tmp_path / "eval"
    for i, sec in enumerate([10.0, 20.0, 100.0, 200.0, 300.0]):
        _write_log(ev, "r1", "m", "x%d" % i, sec)
    s = summarize_harness_eval_from_eval_dir(ev)
    assert s["n_parsed"] == 5
    assert s["summary"] is not None
    assert s["summary"]["median"] == 100.0
    assert s["summary"]["n"] == 5
    assert len(s["harness_seconds_per_instance"]) == 5


def test_empty_eval_dir():
    ev = Path("/nonexistent_harness_eval_xyz")
    s = summarize_harness_eval_from_eval_dir(ev)
    assert s["n_parsed"] == 0
    assert s["summary"] is None
    assert s["harness_seconds_per_instance"] == {}


def test_aggregate_includes_harness_eval():
    from experiments.scripts.compare_runs import aggregate
    from tests.fixtures.gen_fake_runpair import make_fake_runpair

    r = make_fake_runpair(
        run_id="r1",
        instance_ids=["a", "b"],
        n_resolved_baseline=1,
        n_resolved_pf=1,
        n_applies_false=0,
    )
    try:
        be = r / "baseline" / "eval"
        pe = r / "pf" / "eval"
        _write_log(be, "ev1", "pf-swebench-openhands", "a", 55.5)
        _write_log(pe, "ev1", "pf-swebench-openhands", "b", 66.0)
        rep = aggregate(be, pe, r / "baseline" / "r1", r / "pf" / "r1")
        hb = rep["harness_eval"]["baseline"]
        assert hb["harness_seconds_per_instance"].get("a") == 55.5
        hp = rep["harness_eval"]["pf"]
        assert hp["harness_seconds_per_instance"].get("b") == 66.0
    finally:
        shutil.rmtree(r, ignore_errors=True)
