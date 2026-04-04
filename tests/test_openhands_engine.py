# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import platform
import sys
import tempfile
from pathlib import Path
from unittest import mock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
BENCH_SWEBENCH = REPO_ROOT / "bench" / "swebench"
if str(BENCH_SWEBENCH) not in sys.path:
    sys.path.insert(0, str(BENCH_SWEBENCH))


def _is_like_diff(text: str) -> bool:
    if not text or not text.strip():
        return False
    t = text.strip()
    return "diff --git" in t or "--- " in t or t.startswith("---") or "\n@@ " in t


def test_is_like_diff_rejects_non_diff():
    assert _is_like_diff("") is False
    assert _is_like_diff("   \n  ") is False
    assert _is_like_diff("not a patch at all") is False


def test_is_like_diff_accepts_minimal_diff():
    assert _is_like_diff("diff --git a/x b/x\nindex 1..2\n--- a/x\n+++ b/x\n@@ -1,1 +1,1 @@\n") is True
    assert _is_like_diff("--- a/file\n+++ b/file\n@@ -1 +1 @@\n") is True
    assert _is_like_diff("--- a/x\n+++ b/x\n@@ -1,3 +1,3 @@\n") is True


@pytest.mark.skipif(platform.system() == "Windows", reason="subprocess timeout differs on Windows")
def test_get_patch_from_repo_timeout_fallback():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        repo_dir = Path(td)
        (repo_dir / ".git").mkdir()
        with mock.patch.object(openhands_engine.subprocess, "run") as m_run:
            m_run.side_effect = openhands_engine.subprocess.TimeoutExpired("git diff HEAD", 1)
            out = openhands_engine._get_patch_from_repo(repo_dir, timeout=1)
    assert "# git diff failed" in out


def test_parse_trajectory_missing_file_returns_empty_trace():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "nonexistent.jsonl"
        trace = openhands_engine._parse_trajectory_for_trace(path)
    assert trace.prompts_sent == []
    assert trace.tool_calls == []
    assert trace.files_modified == []


def test_parse_trajectory_invalid_jsonl_returns_empty_trace():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "trajectory.jsonl"
        path.write_text("not valid json\n{{{]\n", encoding="utf-8")
        trace = openhands_engine._parse_trajectory_for_trace(path)
    assert trace.raw_events == []


def test_parse_trajectory_valid_jsonl_extracts_events():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        path = Path(td) / "trajectory.jsonl"
        path.write_text(
            json.dumps({"type": "action", "action": "edit", "path": "src/foo.py"}) + "\n",
            encoding="utf-8",
        )
        trace = openhands_engine._parse_trajectory_for_trace(path)
    assert len(trace.raw_events) == 1
    assert "src/foo.py" in (trace.files_modified or [])


def test_solve_sets_execution_mode_for_prime_intellect_subprocess():
    """Prime runs must go through subprocess path and must emit execution metadata."""
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        (ws / "repo").mkdir()
        (ws / "scratch").mkdir()

        fake_trace = openhands_engine.EngineTrace()
        with mock.patch.object(openhands_engine, "_normalize_provider", return_value="prime_intellect"):
            with mock.patch.object(
                openhands_engine,
                "_run_openhands_subprocess",
                return_value=("", fake_trace, True, None, "", ""),
            ):
                res = openhands_engine.solve(
                    workspace_path=ws,
                    task_text="task",
                    config=openhands_engine.OpenHandsConfig(timeout_seconds=1),
                    extra_env=None,
                )

        assert res.success is True
        assert res.trace.execution_mode == "prime_subprocess"
        assert res.trace.cli_mode_forced is True
        assert "prime_intellect" in (res.trace.mode_reason or "").lower()
        assert isinstance(res.trace.openhands_library_core_available, bool)


def test_subprocess_timeout_sets_timeout_origin_on_trace():
    """TimeoutExpired in subprocess mode must attribute to subprocess_wall_timeout."""
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        repo_dir = Path(td) / "repo"
        repo_dir.mkdir()
        scratch_dir = Path(td) / "scratch"
        scratch_dir.mkdir()

        config = openhands_engine.OpenHandsConfig(timeout_seconds=42, max_iterations=1)

        with (
            mock.patch.object(openhands_engine, "_llm_credentials", return_value=("pit_x", "", "prime_intellect")),
            mock.patch.object(openhands_engine, "_openhands_litellm_model", side_effect=lambda prov, m: m),
            mock.patch.object(openhands_engine, "_parse_trajectory_for_trace", return_value=openhands_engine.EngineTrace()),
            mock.patch.object(openhands_engine, "_get_files_modified_from_repo", return_value=[]),
            mock.patch.object(openhands_engine, "_get_patch_from_repo", return_value=""),
            mock.patch.object(
                openhands_engine.subprocess,
                "run",
                side_effect=openhands_engine.subprocess.TimeoutExpired(
                    cmd=["openhands"],
                    timeout=10,
                    output="",
                    stderr="",
                ),
            ),
        ):
            _patch_str, trace, success, err, _stdout, _stderr = openhands_engine._run_openhands_subprocess(
                repo_dir=repo_dir,
                task_text="task",
                config=config,
                scratch_dir=scratch_dir,
                extra_env=None,
            )

        assert success is False
        assert trace.timeout_origin == "subprocess_wall_timeout"
        assert trace.subprocess_timeout_seconds == 42


def test_solve_sets_first_action_latency_and_budgets_from_trace_events():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        (ws / "repo").mkdir()
        (ws / "scratch").mkdir()

        raw_events = [
            {"timestamp": "2026-01-01T00:00:00Z", "kind": "MessageEvent"},
            {"timestamp": "2026-01-01T00:00:05Z", "kind": "ActionEvent", "tool_name": "run_terminal_cmd"},
            {"timestamp": "2026-01-01T00:00:07Z", "kind": "ActionEvent", "tool_name": "edit_file"},
        ]
        fake_trace = openhands_engine.EngineTrace(raw_events=raw_events)

        with mock.patch.object(openhands_engine, "_normalize_provider", return_value="prime_intellect"):
            with mock.patch.object(
                openhands_engine,
                "_run_openhands_subprocess",
                return_value=("", fake_trace, True, None, "", ""),
            ):
                res = openhands_engine.solve(
                    workspace_path=ws,
                    task_text="task",
                    config=openhands_engine.OpenHandsConfig(timeout_seconds=100, max_iterations=1),
                    extra_env=None,
                )

        assert res.success is True
        assert res.trace.startup_budget_s is not None
        assert res.trace.action_budget_s is not None
        assert res.trace.finalization_budget_s is not None
        assert res.trace.first_action_latency_s == 5.0
        assert res.trace.first_file_edit_latency_s == 7.0


def test_solve_sets_timeout_snapshot_when_timeout_origin_present():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        ws = Path(td)
        (ws / "repo").mkdir()
        (ws / "scratch").mkdir()

        raw_events = [
            {"timestamp": "2026-01-01T00:00:00Z", "kind": "MessageEvent", "action": {"message": "boot"}},
            {"timestamp": "2026-01-01T00:00:03Z", "kind": "ActionEvent", "tool_name": "edit_file", "action": {"name": "edit_file"}},
            {"timestamp": "2026-01-01T00:00:05Z", "kind": "MessageEvent", "observation": "still running..."},
        ]
        fake_trace = openhands_engine.EngineTrace(raw_events=raw_events)
        fake_trace.timeout_origin = "subprocess_wall_timeout"

        with mock.patch.object(openhands_engine, "_normalize_provider", return_value="prime_intellect"):
            with mock.patch.object(
                openhands_engine,
                "_run_openhands_subprocess",
                return_value=("", fake_trace, False, "timed out", "", ""),
            ):
                res = openhands_engine.solve(
                    workspace_path=ws,
                    task_text="task",
                    config=openhands_engine.OpenHandsConfig(timeout_seconds=60, max_iterations=1),
                    extra_env=None,
                )

        assert res.success is False
        assert res.trace.timeout_snapshot is not None
        assert res.trace.timeout_snapshot.get("tail_event_count") is not None


def test_path_restricted_fallback_when_diff_stat_over_threshold():
    from bench.swebench.engines import openhands_engine

    with tempfile.TemporaryDirectory() as td:
        repo_dir = Path(td)
        (repo_dir / ".git").mkdir()
        scratch_dir = Path(td) / "scratch"
        scratch_dir.mkdir()
        paths_300 = [f"f{i}.py" for i in range(300)]
        config = openhands_engine.OpenHandsConfig(timeout_seconds=60)
        big_patch = "x" * (openhands_engine.MAX_PATCH_BYTES + 1)
        small_patch = "diff --git a/f0.py b/f0.py\n--- a/f0.py\n+++ b/f0.py\n@@ -0,0 +1,1 @@\n+x\n"

        trajectory_stdout = "\n".join(
            json.dumps({"type": "action", "action": "edit", "path": p})
            for p in paths_300
        )
        with mock.patch.object(
            openhands_engine,
            "_get_diff_stat_file_count",
            return_value=250,
        ):
            with mock.patch.object(
                openhands_engine,
                "_get_patch_from_repo_for_paths",
                side_effect=[big_patch, small_patch],
            ) as m_paths:
                with mock.patch.object(
                    openhands_engine.subprocess,
                    "run",
                    return_value=mock.Mock(
                        returncode=0, stdout=trajectory_stdout, stderr=""
                    ),
                ):
                    patch_str, trace, success, err, stdout, stderr = (
                        openhands_engine._run_openhands_subprocess(
                            repo_dir, "fix the bug", config, scratch_dir
                        )
                    )
                assert m_paths.call_count >= 2
                second_call_paths = m_paths.call_args_list[1][0][1]
                assert len(second_call_paths) == openhands_engine.PATH_RESTRICTED_MAX_PATHS_FALLBACK
                assert patch_str == small_patch
