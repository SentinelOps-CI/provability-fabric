# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Integration: `run_engine_for_instance` with mock engine and minimal workspace.

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.runner import run_engine_for_instance
from tests.fixtures.mock_engine import make_instance_dict
from tests.fixtures.mock_workspace import make_minimal_workspace_root


def test_run_engine_mock_returns_trace_and_patch(tmp_path: Path) -> None:
    ws = make_minimal_workspace_root(tmp_path)
    inst = make_instance_dict("integration__mock-1")
    run_dir = tmp_path / "runs" / "r1"
    run_dir.mkdir(parents=True)
    patch, log, trace = run_engine_for_instance(
        inst,
        "mock",
        run_dir,
        inst["instance_id"],
        workspace_path=ws,
        task_text="Fix the bug",
        openhands_config=None,
        openhands_extra_env=None,
    )
    assert trace is not None
    assert isinstance(patch, str)
    assert "Engine=mock" in log or "mock" in log.lower()
    assert "tool_calls" in trace or trace.get("error")
