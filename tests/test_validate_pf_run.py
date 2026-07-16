# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Unit tests for validate_pf_run: minimal PF dir passes; missing compliance fails.

from __future__ import annotations

import json
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from bench.swebench.validate_pf_run import validate_run
from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_validate_pf_run_passes_with_compliance():
    root = make_fake_runpair(instance_ids=["a"], n_resolved_pf=1)
    try:
        pf_run_dir = root / "pf" / "fake-run-001"
        ok, messages = validate_run(pf_run_dir)
        assert ok is True, messages
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_validate_pf_run_fails_when_compliance_missing():
    root = make_fake_runpair(instance_ids=["a"])
    try:
        pf_run_dir = root / "pf" / "fake-run-001"
        inst_dirs = sorted(d for d in pf_run_dir.iterdir() if d.is_dir())
        assert inst_dirs, "expected at least one instance directory"
        (inst_dirs[0] / "policy_compliance_summary.json").unlink(missing_ok=True)
        ok, messages = validate_run(pf_run_dir)
        assert ok is False
        assert any("policy_compliance_summary" in m or "compliance" in m.lower() for m in messages)
    finally:
        shutil.rmtree(root, ignore_errors=True)
