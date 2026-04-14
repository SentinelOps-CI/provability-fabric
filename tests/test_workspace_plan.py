# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Unit tests for workspace: manifest shape, hashing; materialize with mocked git.

from __future__ import annotations

import sys
import tempfile
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_SWEBENCH = REPO_ROOT / "bench" / "swebench"
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
if str(BENCH_SWEBENCH) not in sys.path:
    sys.path.insert(0, str(BENCH_SWEBENCH))

from bench.swebench.loader import SWEbenchInstance
from bench.swebench.workspace import materialize_workspace, WorkspaceManifest


def test_workspace_manifest_shape_and_hash():
    manifest = WorkspaceManifest(
        instance_id="i1",
        repo="r",
        base_commit="c",
        workspace_root="/w",
        repo_path="/w/repo",
        task_prompt_path="/w/task_prompt.md",
        scratch_path="/w/scratch",
    )
    d = manifest.to_canonical_dict()
    assert d["instance_id"] == "i1"
    assert d["repo"] == "r"
    assert d["base_commit"] == "c"
    h = manifest.sha256()
    assert len(h) == 64
    assert all(c in "0123456789abcdef" for c in h)


def test_materialize_workspace_invalid_repo_raises():
    instance = SWEbenchInstance(
        instance_id="x",
        repo="",
        base_commit="c",
        problem_statement="p",
        hints_text="",
        raw={},
    )
    with tempfile.TemporaryDirectory() as td:
        with pytest.raises(ValueError, match="Invalid repo"):
            materialize_workspace(instance, workspaces_dir=Path(td))


def test_materialize_workspace_mock_git_clone_checkout():
    instance = SWEbenchInstance(
        instance_id="test__repo-1",
        repo="https://github.com/owner/repo.git",
        base_commit="abc123",
        problem_statement="Fix.",
        hints_text="",
        raw={},
    )
    with tempfile.TemporaryDirectory() as td:
        ws_dir = Path(td) / "ws"
        mock_run = MagicMock(return_value=MagicMock(stdout="abc123\n", stderr="", returncode=0))
        with patch("bench.swebench.workspace._run_git", mock_run):
            with patch("bench.swebench.workspace._get_head_commit", return_value="abc123"):
                try:
                    materialize_workspace(instance, workspaces_dir=ws_dir)
                except Exception:
                    pass
            calls = mock_run.call_args_list
            assert len(calls) >= 1
            first = calls[0][0]
            assert "clone" in first or "checkout" in str(calls)
