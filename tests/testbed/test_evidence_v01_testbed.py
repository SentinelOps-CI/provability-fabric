#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Public testbed wrapper tests."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
TESTBED = REPO / "testbed" / "evidence-v0.1"


def _bash_exe() -> str | None:
    git_bash = Path(os.environ.get("ProgramFiles", r"C:\Program Files")) / "Git" / "bin" / "bash.exe"
    if git_bash.is_file():
        return str(git_bash)
    return shutil.which("bash")


def _run_testbed_script(name: str) -> subprocess.CompletedProcess[str]:
    bash = _bash_exe()
    assert bash is not None
    # Use a repo-relative path so Git Bash on Windows can execute the script.
    script = f"testbed/evidence-v0.1/{name}"
    return subprocess.run([bash, "-c", f"bash {script}"], cwd=REPO, text=True)


@pytest.mark.skipif(_bash_exe() is None, reason="bash required")
def test_happy_path_script() -> None:
    proc = _run_testbed_script("run_happy_path.sh")
    assert proc.returncode == 0


@pytest.mark.skipif(_bash_exe() is None, reason="bash required")
def test_tamper_script() -> None:
    proc = _run_testbed_script("run_tamper_case.sh")
    assert proc.returncode == 0
