# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Lightweight integration-style checks (no full harness).

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.runner import run_patch_apply_check


def test_patch_apply_check_empty_patch_no_repo_returns_false():
    # Non-repo path: should not crash; applies False
    applies, rep = run_patch_apply_check(Path("/nonexistent/path/that/should/not/exist"), "", "a", "b")
    assert applies is False
    assert "applies" in rep


def test_workspace_manager_cleanup_is_noop(tmp_path: Path):
    from bench.swebench.workspace_manager import WorkspaceManager

    mgr = WorkspaceManager(workspaces_dir=tmp_path)
    p = tmp_path / "dummy"
    p.mkdir()
    mgr.cleanup(p)  # documented no-op; must not raise
    assert p.is_dir()
