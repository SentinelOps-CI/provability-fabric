#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Proof test for P12: solver-disabled mode must not emit fake patch content.

import shutil
import sys
import tempfile
from pathlib import Path

# Run from bench/swebench so imports resolve
BENCH_DIR = Path(__file__).resolve().parent
if str(BENCH_DIR) not in sys.path:
    sys.path.insert(0, str(BENCH_DIR))

from runner import run_engine_for_instance, _solver_disabled_patch


def test_solver_disabled_patch_content():
    """_solver_disabled_patch must return content with solver_disabled and no fake patch wording."""
    instance = {"instance_id": "test-123", "repo": "org/repo", "base_commit": "abc"}
    out = _solver_disabled_patch(instance, "mock")
    assert "solver_disabled" in out, "solver_disabled mode must be clearly marked"
    assert "engine=mock" in out or "mock" in out
    assert "Placeholder patch" not in out
    assert "Stub patch" not in out
    assert "placeholder" not in out.lower() or "solver_disabled" in out


def test_solver_disabled_mode():
    """Solver-disabled or mock output must never contain fake patch wording (Placeholder/Stub patch)."""
    instance = {"instance_id": "swe-test-001", "repo": "test/repo", "base_commit": "deadbeef"}
    run_dir = Path(tempfile.mkdtemp(prefix="pf_swebench_test_"))
    try:
        patch, log_text, trace = run_engine_for_instance(
            instance,
            engine="mock",
            run_dir=run_dir,
            instance_id="swe-test-001",
            workspace_path=None,
            task_text="",
        )
        # Either explicit solver_disabled marker or real mock output; never fake patch text
        assert "Placeholder patch" not in patch, "gate: no Placeholder patch in output"
        assert "Stub patch from PF runner" not in patch, "gate: no Stub patch in output"
        assert "solver_disabled" in patch or "mock_success" in log_text or len(patch.strip()) > 0
    finally:
        shutil.rmtree(run_dir, ignore_errors=True)
