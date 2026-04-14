# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Unit tests for check_no_stub: stub in model.patch fails; clean dirs pass.

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from tests.fixtures.gen_fake_runpair import make_fake_runpair


def test_check_no_stub_fails_when_stub_present():
    root = make_fake_runpair(instance_ids=["a"], stub_in_patch=True)
    try:
        script = REPO_ROOT / "experiments" / "scripts" / "check_no_stub.py"
        proc = subprocess.run(
            [sys.executable, str(script), str(root / "baseline")],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode != 0
        assert ".swebench_stub" in (proc.stderr or "")
    finally:
        shutil.rmtree(root, ignore_errors=True)


def test_check_no_stub_passes_when_clean():
    root = make_fake_runpair(instance_ids=["a"], stub_in_patch=False)
    try:
        script = REPO_ROOT / "experiments" / "scripts" / "check_no_stub.py"
        proc = subprocess.run(
            [sys.executable, str(script), str(root / "baseline"), str(root / "pf")],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        assert proc.returncode == 0
    finally:
        shutil.rmtree(root, ignore_errors=True)
