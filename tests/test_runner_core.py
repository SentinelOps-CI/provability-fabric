# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import sys
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.run_config import RunConfig
from bench.swebench.runner_core import run_swebench


def test_run_swebench_delegates_to_execute_run():
    cfg = RunConfig(engine="mock", mode="deterministic", dataset="Lite", split="test")
    with patch("bench.swebench.runner._execute_run", return_value=0) as ex:
        assert run_swebench(cfg) == 0
        ex.assert_called_once_with(cfg)


def test_run_swebench_propagates_return_code():
    cfg = RunConfig(engine="mock", mode="deterministic")
    with patch("bench.swebench.runner._execute_run", return_value=2):
        assert run_swebench(cfg) == 2
