# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path
from unittest import mock


REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def test_runner_direct_agent_no_fallback_on_quality_failure(tmp_path: Path):
    from bench.swebench import runner
    from bench.swebench.engines.openhands_engine import EngineTrace, SolveResult

    ws = tmp_path / "ws"
    (ws / "repo").mkdir(parents=True)
    (ws / "scratch").mkdir(parents=True)

    da_result = SolveResult(
        patch_diff_str="",
        trace=EngineTrace(raw_events=[{"kind": "MessageEvent", "timestamp": 1}]),
        success=False,
        error="empty patch",
    )
    with (
        mock.patch.object(runner, "direct_agent_solve", return_value=da_result),
        mock.patch.object(runner, "openhands_solve") as m_oh,
    ):
        patch, log_text, trace = runner.run_engine_for_instance(
            instance_dict={"instance_id": "x", "repo": "r", "base_commit": "c"},
            engine="direct_agent",
            run_dir=tmp_path,
            instance_id="x",
            workspace_path=ws,
            task_text="fix",
            openhands_config=None,
            openhands_extra_env=None,
        )

    assert "fallback_openhands_invoked=1" not in log_text
    assert patch == ""
    assert trace is not None
    assert trace.get("fallback_invoked") is None
    assert m_oh.call_count == 0


def test_runner_direct_agent_no_fallback_when_patch_present(tmp_path: Path):
    from bench.swebench import runner
    from bench.swebench.engines.openhands_engine import EngineTrace, SolveResult

    ws = tmp_path / "ws"
    (ws / "repo").mkdir(parents=True)
    (ws / "scratch").mkdir(parents=True)

    da_result = SolveResult(
        patch_diff_str="diff --git a/x b/x\n--- a/x\n+++ b/x\n@@ -1 +1 @@\n-a\n+b\n",
        trace=EngineTrace(raw_events=[{"kind": "ActionEvent", "timestamp": 1}], files_modified=["x"]),
        success=True,
        error=None,
    )
    with (
        mock.patch.object(runner, "direct_agent_solve", return_value=da_result),
        mock.patch.object(runner, "openhands_solve") as m_oh,
    ):
        patch, log_text, trace = runner.run_engine_for_instance(
            instance_dict={"instance_id": "x", "repo": "r", "base_commit": "c"},
            engine="direct_agent",
            run_dir=tmp_path,
            instance_id="x",
            workspace_path=ws,
            task_text="fix",
            openhands_config=None,
            openhands_extra_env=None,
        )
    assert patch.startswith("diff --git")
    assert "fallback_openhands_invoked=1" not in log_text
    assert trace is not None
    assert not trace.get("fallback_invoked")
    assert m_oh.call_count == 0


def test_runner_direct_agent_fallback_on_provider_fault(tmp_path: Path):
    from bench.swebench import runner
    from bench.swebench.engines.openhands_engine import EngineTrace, SolveResult

    ws = tmp_path / "ws"
    (ws / "repo").mkdir(parents=True)
    (ws / "scratch").mkdir(parents=True)
    da_result = SolveResult(
        patch_diff_str="",
        trace=EngineTrace(raw_events=[]),
        success=False,
        error="HTTPError 429 rate limit",
    )
    oh_result = SolveResult(
        patch_diff_str="diff --git a/x b/x\n--- a/x\n+++ b/x\n@@ -1 +1 @@\n-a\n+b\n",
        trace=EngineTrace(raw_events=[{"kind": "ActionEvent", "timestamp": 2}], files_modified=["x"]),
        success=True,
        error=None,
    )
    with (
        mock.patch.object(runner, "direct_agent_solve", return_value=da_result),
        mock.patch.object(runner, "openhands_solve", return_value=oh_result),
    ):
        patch, log_text, trace = runner.run_engine_for_instance(
            instance_dict={"instance_id": "x", "repo": "r", "base_commit": "c"},
            engine="direct_agent",
            run_dir=tmp_path,
            instance_id="x",
            workspace_path=ws,
            task_text="fix",
            openhands_config=None,
            openhands_extra_env=None,
        )
    assert "fallback_openhands_invoked=1" in log_text
    assert patch.startswith("diff --git")
    assert trace is not None
    assert trace.get("fallback_reason_type") == "runtime_or_provider"

