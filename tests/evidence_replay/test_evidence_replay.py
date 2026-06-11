#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Evidence replay CLI tests."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
VALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "valid" / "basic-evidence-bundle.json"
INVALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "invalid" / "bad-bundle-digest.json"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def test_replay_valid(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "replay.json"
    proc = subprocess.run(
        [str(pf_bin), "evidence", "replay", "--bundle", str(VALID), "--out", str(out)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout


def test_replay_tampered_fails(pf_bin: Path) -> None:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "replay", "--bundle", str(INVALID)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode != 0
