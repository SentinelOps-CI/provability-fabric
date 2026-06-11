#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Strict validation tests for pf evidence validate."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
VALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "valid" / "basic-evidence-bundle.json"
INVALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "invalid"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def run_pf(pf_bin: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(pf_bin), *args], cwd=REPO, text=True, capture_output=True)


def test_validate_valid_bundle_strict(pf_bin: Path) -> None:
    proc = run_pf(pf_bin, "evidence", "validate", str(VALID), "--strict")
    assert proc.returncode == 0, proc.stderr + proc.stdout


def test_validate_missing_artifact_fails(pf_bin: Path) -> None:
    proc = run_pf(pf_bin, "evidence", "validate", str(INVALID / "missing-artifacts.json"), "--strict")
    assert proc.returncode != 0


def test_validate_tampered_bundle_digest_fails(pf_bin: Path) -> None:
    proc = run_pf(pf_bin, "evidence", "validate", str(INVALID / "bad-bundle-digest.json"), "--strict")
    assert proc.returncode != 0


def test_validate_emits_report(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "report.json"
    proc = run_pf(pf_bin, "evidence", "validate", str(VALID), "--strict", "--report-out", str(out))
    assert proc.returncode == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "pass"
