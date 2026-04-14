# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

from __future__ import annotations

import json
import platform
import sys
import tempfile
from pathlib import Path
from unittest.mock import Mock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.run_config import RunConfig, build_argument_parser  # noqa: E402


def test_build_argument_parser_has_expected_flags():
    p = build_argument_parser()
    opts = {a.dest for a in p._actions if hasattr(a, "dest") and a.dest}
    assert "dataset" in opts
    assert "engine" in opts
    assert "runs_dir" in opts


def test_run_config_defaults():
    """Test RunConfig with default values."""
    config = RunConfig()
    assert config.dataset == "Lite"
    assert config.split == "test"
    assert config.engine == "openhands"
    assert config.mode == "default"
    assert config.guarded is False
    assert config.effective_guarded is False
    assert config.openhands_timeout == 1200


def test_run_config_custom_values():
    """Test RunConfig with custom values."""
    config = RunConfig(
        dataset="Verified",
        split="dev",
        engine="mock",
        mode="pf_guarded",
        guarded=True,
        max_instances=10,
    )
    assert config.dataset == "Verified"
    assert config.split == "dev"
    assert config.engine == "mock"
    assert config.mode == "pf_guarded"
    assert config.guarded is True
    assert config.effective_guarded is True
    assert config.max_instances == 10


def test_run_config_pf_guarded_defaults_policy():
    """Test that pf_guarded mode defaults policy to swebench_safe_v1."""
    config = RunConfig(mode="pf_guarded", policy="")
    assert config.policy == "swebench_safe_v1"
    assert config.effective_guarded is True


def test_run_config_pf_guarded_preserves_explicit_policy():
    """Test that explicit policy is preserved in pf_guarded mode."""
    config = RunConfig(mode="pf_guarded", policy="custom_policy")
    assert config.policy == "custom_policy"
    assert config.effective_guarded is True


def test_run_config_instance_ids_parsing():
    """Test parsing of instance_ids from comma-separated string."""
    config = RunConfig(instance_ids="id1,id2,id3")
    assert config.instance_id_list == ["id1", "id2", "id3"]


def test_run_config_instance_ids_file(tmp_path: Path):
    """Test loading instance_ids from file."""
    ids_file = tmp_path / "instance_ids.txt"
    ids_file.write_text("id1\nid2\nid3\n", encoding="utf-8")
    config = RunConfig(instance_ids_file=str(ids_file))
    assert config.instance_id_list == ["id1", "id2", "id3"]


def test_run_config_instance_ids_file_not_found():
    """Test error when instance_ids_file doesn't exist."""
    with pytest.raises(ValueError, match="not found"):
        RunConfig(instance_ids_file="/nonexistent/file.txt")


def test_run_config_dataset_normalization():
    """Test dataset name normalization (case-insensitive)."""
    config_lower = RunConfig(dataset="lite")
    assert config_lower.dataset == "Lite"

    config_upper = RunConfig(dataset="VERIFIED")
    assert config_upper.dataset == "Verified"

    config_mixed = RunConfig(dataset="FuLl")
    assert config_mixed.dataset == "Full"


def test_run_config_manifest_budgets():
    """Test applying budgets from manifest.json."""
    with tempfile.TemporaryDirectory() as tmpdir:
        manifest_path = Path(tmpdir) / "manifest.json"
        manifest = {
            "budgets": {"max_steps": 50, "timeout_sec": 1800},
            "model": {"id": "gpt-4o"},
        }
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")

        config = RunConfig(
            experiment_dir=tmpdir,
            manifest_argv=["runner.py", "--experiment-dir", tmpdir],
        )
        assert config.openhands_max_iterations == 50
        assert config.openhands_timeout == 1800
        assert config.openhands_model == "gpt-4o"


def test_run_config_manifest_budgets_missing_file():
    """Test that missing manifest.json doesn't cause errors."""
    with tempfile.TemporaryDirectory() as tmpdir:
        config = RunConfig(experiment_dir=tmpdir)
        # Should use defaults
        assert config.openhands_max_iterations == 25
        assert config.openhands_timeout == 1200


def test_run_config_validate_valid():
    """Test validation with valid configuration."""
    engine = "mock" if platform.system() == "Windows" else "openhands"
    config = RunConfig(dataset="Lite", mode="default", engine=engine)
    errors = config.validate()
    assert len(errors) == 0


def test_run_config_validate_invalid_dataset():
    """Test validation with invalid dataset."""
    config = RunConfig(dataset="InvalidDataset")
    errors = config.validate()
    assert len(errors) > 0
    assert any("dataset" in err.lower() for err in errors)


def test_run_config_validate_invalid_mode():
    """Test validation with invalid mode."""
    config = RunConfig(mode="invalid_mode")
    errors = config.validate()
    assert len(errors) > 0
    assert any("mode" in err.lower() for err in errors)


def test_run_config_validate_invalid_engine():
    """Test validation with invalid engine."""
    config = RunConfig(engine="invalid_engine")
    errors = config.validate()
    assert len(errors) > 0
    assert any("engine" in err.lower() for err in errors)


def test_run_config_validate_direct_agent_engine():
    engine = "mock" if platform.system() == "Windows" else "direct_agent"
    config = RunConfig(dataset="Lite", mode="default", engine=engine)
    errors = config.validate()
    assert len(errors) == 0


def test_run_config_from_args():
    """Test creating RunConfig from argparse.Namespace."""
    args = Mock()
    args.dataset = "Verified"
    args.split = "test"
    args.engine = "mock"
    args.mode = "default"
    args.guarded = False
    args.policy = ""
    args.instance_ids = ""
    args.instance_ids_file = ""
    args.max_instances = None
    args.instances_file = ""
    args.experiment_dir = ""
    args.seed = None
    args.out = "predictions.jsonl"
    args.runs_dir = "runs"
    args.run_id = ""
    args.workspaces_dir = "workspaces"
    args.dataset_cache_dir = ""
    args.openhands_model = "gpt-4o-mini"
    args.openhands_max_iterations = 25
    args.openhands_timeout = 900
    args.prove = False
    args.proofs_dir = ""
    args.no_workspace = False
    args.skip_existing = False
    args.preflight = False

    config = RunConfig.from_args(args)
    assert config.dataset == "Verified"
    assert config.engine == "mock"
    assert config.mode == "default"


def test_run_config_to_dict():
    """Test converting RunConfig to dictionary."""
    config = RunConfig(
        dataset="Lite",
        engine="mock",
        max_instances=5,
        guarded=True,
    )
    config_dict = config.to_dict()
    assert config_dict["dataset"] == "Lite"
    assert config_dict["engine"] == "mock"
    assert config_dict["max_instances"] == 5
    assert config_dict["guarded"] is True
    # Computed fields should not be in dict
    assert "effective_guarded" not in config_dict
    assert "instance_id_list" not in config_dict
