# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Workspace materialization failure paths (mocked; no network/git).

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

import bench.swebench.workspace_manager as wm_mod
from bench.swebench.workspace_manager import WorkspaceManager


def test_workspace_manager_materialize_propagates_os_error():
    inst = MagicMock()
    inst.instance_id = "x__y-1"
    with patch.object(wm_mod, "_materialize_workspace", side_effect=OSError("simulated disk full")):
        mgr = WorkspaceManager(workspaces_dir="/tmp/pf_ws_test")
        with pytest.raises(OSError, match="simulated disk full"):
            mgr.materialize(inst)


def test_workspace_manager_materialize_propagates_value_error():
    inst = MagicMock()
    inst.instance_id = "a__b-2"
    with patch.object(wm_mod, "_materialize_workspace", side_effect=ValueError("bad manifest")):
        mgr = WorkspaceManager(workspaces_dir="/tmp/pf_ws_test")
        with pytest.raises(ValueError, match="bad manifest"):
            mgr.materialize(inst)
