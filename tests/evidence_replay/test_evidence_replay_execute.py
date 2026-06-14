#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Deep replay execute tests (requires TRACE-REPLAY-KIT submodule)."""

from __future__ import annotations

import json
import platform
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
BUNDLE = REPO / "specs" / "evidence" / "v0.2" / "examples" / "valid" / "deep-replay-bundle.json"
KIT_RUNNER = REPO / "external" / "TRACE-REPLAY-KIT" / "runner" / "replay_run.py"


def _pf_bin() -> Path:
    for candidate in (PF, REPO / "core" / "cli" / "pf" / "pf.exe"):
        if candidate.exists():
            return candidate
    subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    return _pf_bin()


@pytest.mark.skipif(platform.system() == "Windows", reason="KIT execute replay runs on Linux CI")
@pytest.mark.skipif(not KIT_RUNNER.is_file(), reason="TRACE-REPLAY-KIT missing (make submodules)")
def test_evidence_replay_execute_low_view(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "replay-report.json"
    proc = subprocess.run(
        [
            str(pf_bin),
            "evidence",
            "replay",
            "--bundle",
            str(BUNDLE),
            "--base-dir",
            str(BUNDLE.parent),
            "--execute",
            "--low-view",
            "--out-dir",
            str(tmp_path / "kit-out"),
            "--out",
            str(out),
            "--json",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "pass"
    assert report.get("execute_status") == "pass"
    assert report.get("low_view_result") == "pass"
