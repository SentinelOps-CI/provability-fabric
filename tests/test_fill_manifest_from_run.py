# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
# Contract tests for fill_manifest_from_run.py: writes pf_commit, created_at; copies agent_commit from env; writes to run_dir.

from __future__ import annotations

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest import mock

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


def test_fill_manifest_writes_pf_commit_and_created_at(tmp_path):
    """Script writes pf_commit and created_at to manifest."""
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"experiment_id": "exp1", "agent_commit": ""}, indent=2), encoding="utf-8")
    with mock.patch("experiments.scripts.fill_manifest_from_run.get_git_sha", return_value="abc123def"):
        from experiments.scripts.fill_manifest_from_run import main
        with mock.patch("sys.argv", ["fill_manifest_from_run.py", str(manifest)]):
            code = main()
    assert code == 0
    data = json.loads(manifest.read_text(encoding="utf-8"))
    assert data["pf_commit"] == "abc123def"
    assert "created_at" in data and data["created_at"]


def test_fill_manifest_copies_openhands_commit_from_env(tmp_path):
    """When OPENHANDS_COMMIT (or AGENT_COMMIT) is set, script copies it to agent_commit."""
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"experiment_id": "exp1", "agent_commit": ""}, indent=2), encoding="utf-8")
    with mock.patch("experiments.scripts.fill_manifest_from_run.get_git_sha", return_value="pfsha"):
        with mock.patch.dict(os.environ, {"OPENHANDS_COMMIT": "oh_abc123"}, clear=False):
            from experiments.scripts.fill_manifest_from_run import main
            with mock.patch("sys.argv", ["fill_manifest_from_run.py", str(manifest)]):
                main()
    data = json.loads(manifest.read_text(encoding="utf-8"))
    assert data["agent_commit"] == "oh_abc123"


def test_fill_manifest_writes_experiment_manifest_to_run_dir_when_passed(tmp_path):
    """When run_dir is passed, script writes experiment_manifest.json to that directory."""
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"experiment_id": "exp1"}, indent=2), encoding="utf-8")
    run_dir = tmp_path / "run_dir"
    run_dir.mkdir()
    with mock.patch("experiments.scripts.fill_manifest_from_run.get_git_sha", return_value="sha1"):
        from experiments.scripts.fill_manifest_from_run import main
        with mock.patch("sys.argv", ["fill_manifest_from_run.py", str(manifest), str(run_dir)]):
            code = main()
    assert code == 0
    dest = run_dir / "experiment_manifest.json"
    assert dest.exists()
    data = json.loads(dest.read_text(encoding="utf-8"))
    assert data["pf_commit"] == "sha1"
    assert data["experiment_id"] == "exp1"


def test_fill_manifest_not_in_git_deterministic(tmp_path):
    """When not in a git repo, get_git_sha returns ''; script still writes created_at and does not crash."""
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"experiment_id": "exp1"}, indent=2), encoding="utf-8")
    with mock.patch("experiments.scripts.fill_manifest_from_run.get_git_sha", return_value=""):
        from experiments.scripts.fill_manifest_from_run import main
        with mock.patch("sys.argv", ["fill_manifest_from_run.py", str(manifest)]):
            code = main()
    assert code == 0
    data = json.loads(manifest.read_text(encoding="utf-8"))
    assert data["pf_commit"] == ""
    assert "created_at" in data
