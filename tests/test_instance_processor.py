# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.instance_processor import InstanceProcessor
from bench.swebench.workspace_manager import WorkspaceManager


def test_instance_processor_materialize_delegates():
    wm = MagicMock(spec=WorkspaceManager)
    wm.materialize.return_value = (Path("/w"), MagicMock(), "h")
    proc = InstanceProcessor(wm)
    inst = MagicMock()
    out = proc.materialize_workspace(inst)
    assert out[2] == "h"
    wm.materialize.assert_called_once_with(inst)


def test_instance_processor_run_engine_requires_fn():
    wm = MagicMock(spec=WorkspaceManager)
    proc = InstanceProcessor(wm, run_engine_fn=None)
    with pytest.raises(RuntimeError):  # noqa: PT012
        proc.run_engine({}, "mock", Path("/r"), "id")


def test_instance_processor_run_engine_calls_injected():
    wm = MagicMock(spec=WorkspaceManager)
    fn = MagicMock(return_value=("p", "log", {}))
    proc = InstanceProcessor(wm, run_engine_fn=fn)
    proc.run_engine({"instance_id": "x"}, "mock", Path("/r"), "x", workspace_path=Path("/w"))
    fn.assert_called_once()
