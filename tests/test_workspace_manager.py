# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.util import sanitize_instance_id
from bench.swebench.workspace_manager import WorkspaceManager


def test_workspace_manager_get_workspace_path_matches_sanitize():
    base = Path("rel_workspaces_test")
    mgr = WorkspaceManager(workspaces_dir=base)
    iid = "org/repo-123"
    expected = (base / sanitize_instance_id(iid)).resolve()
    assert mgr.get_workspace_path(iid) == expected


def test_workspace_manager_materialize_delegates():
    import bench.swebench.workspace_manager as wm

    fake_manifest = MagicMock()
    fake_manifest.to_canonical_dict = MagicMock(return_value={})
    with patch.object(wm, "_materialize_workspace") as mat:
        mat.return_value = (Path("/w"), fake_manifest, "abc")
        mgr = WorkspaceManager("wdir")
        inst = MagicMock()
        inst.instance_id = "x"
        root, man, h = mgr.materialize(inst)
        assert root == Path("/w")
        assert h == "abc"
        mat.assert_called_once_with(inst, workspaces_dir=Path("wdir"), force_refresh=False)
