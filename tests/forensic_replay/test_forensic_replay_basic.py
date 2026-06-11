#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Forensic replay example tests."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
PASS = REPO / "examples" / "forensic-replay-basic" / "basic-evidence-bundle.json"
TAMPER = REPO / "examples" / "forensic-replay-basic" / "tampered-bundle.json"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def test_forensic_pass_case(pf_bin: Path) -> None:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "replay", "--bundle", str(PASS)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr


def test_forensic_tamper_case(pf_bin: Path) -> None:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "replay", "--bundle", str(TAMPER)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode != 0
