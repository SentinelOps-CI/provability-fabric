# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def test_resolved_runner_model_env_over_cli(monkeypatch):
    from experiments.scripts.run_direct_agent_ab_gate import _resolved_runner_model

    monkeypatch.delenv("OPENHANDS_MODEL", raising=False)
    assert _resolved_runner_model("cli-model") == "cli-model"
    monkeypatch.setenv("OPENHANDS_MODEL", "env-model")
    assert _resolved_runner_model("cli-model") == "env-model"


def test_default_ab_checkpoint_shape():
    from experiments.scripts.run_direct_agent_ab_gate import _default_ab_checkpoint

    ck = _default_ab_checkpoint()
    assert ck["phase"] == "init"
    assert ck["phases"]["baseline"]["status"] == "pending"
    assert ck["phases"]["candidate"]["status"] == "pending"
    assert ck["phases"]["compare"]["status"] == "pending"


def test_instances_with_critical_drop(tmp_path: Path):
    from experiments.scripts.run_direct_agent_ab_gate import _instances_with_critical_drop

    run_dir = tmp_path / "run"
    a = run_dir / "inst_a"
    b = run_dir / "inst_b"
    a.mkdir(parents=True)
    b.mkdir(parents=True)
    (a / "engine_trace.json").write_text(
        json.dumps({"task_delivery_report": {"critical_drop": True}}),
        encoding="utf-8",
    )
    (b / "engine_trace.json").write_text(
        json.dumps({"task_delivery_report": {"critical_drop": False}}),
        encoding="utf-8",
    )

    out = _instances_with_critical_drop(run_dir)
    assert out == ["inst_a"]

