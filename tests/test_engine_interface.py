# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.engines.base import Engine  # noqa: E402
from bench.swebench.engines.mock_engine import MockEngine  # noqa: E402
from bench.swebench.engines.openhands_adapter import DirectAgentEngine  # noqa: E402


def test_mock_engine_is_engine_subclass():
    assert issubclass(MockEngine, Engine)


def test_get_engine_mock():
    from bench.swebench.engines.openhands_adapter import get_engine

    eng = get_engine("mock")
    assert isinstance(eng, MockEngine)


def test_get_engine_unknown():
    from bench.swebench.engines.openhands_adapter import get_engine

    with pytest.raises(ValueError):
        get_engine("not-real")


def test_get_engine_direct_agent():
    from bench.swebench.engines.openhands_adapter import get_engine

    eng = get_engine("direct_agent")
    assert isinstance(eng, DirectAgentEngine)


def test_openhands_engine_requires_workspace():
    from bench.swebench.engines.openhands_adapter import OpenHandsEngine

    oh = OpenHandsEngine()
    with pytest.raises(RuntimeError):
        oh.solve(None, "task")
