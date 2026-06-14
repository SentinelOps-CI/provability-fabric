#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""End-to-end Evidence v0.1 pack -> validate -> tamper."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
EXAMPLE = REPO / "examples" / "evidence-basic"
EXPECTED = EXAMPLE / "expected"
GOLDEN_KEYS = ("status", "errors", "warnings")


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def run_pf(pf_bin: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(pf_bin), *args], cwd=REPO, text=True, capture_output=True)


def test_checked_in_bundle_digest_matches_expected() -> None:
    bundle = json.loads((EXAMPLE / "basic-evidence-bundle.json").read_text(encoding="utf-8"))
    expected_digest = (EXPECTED / "bundle.digest.txt").read_text(encoding="utf-8").strip()
    assert bundle["bundle_digest"] == expected_digest


def test_pack_validate_tamper(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "bundle.json"
    proc = run_pf(
        pf_bin,
        "evidence",
        "bundle",
        "pack",
        "--manifest",
        str(EXAMPLE / "manifest.json"),
        "--out",
        str(out),
    )
    assert proc.returncode == 0, proc.stderr
    proc = run_pf(
        pf_bin,
        "evidence",
        "validate",
        str(out),
        "--strict",
        "--base-dir",
        str(EXAMPLE),
    )
    assert proc.returncode == 0, proc.stderr
    bundle = json.loads(out.read_text(encoding="utf-8"))
    bundle["bundle_digest"] = "sha256:" + "0" * 64
    out.write_text(json.dumps(bundle, indent=2) + "\n", encoding="utf-8")
    proc = run_pf(
        pf_bin,
        "evidence",
        "validate",
        str(out),
        "--strict",
        "--base-dir",
        str(EXAMPLE),
    )
    assert proc.returncode != 0


def test_validate_report_matches_golden(pf_bin: Path, tmp_path: Path) -> None:
    report_out = tmp_path / "report.json"
    proc = run_pf(
        pf_bin,
        "evidence",
        "validate",
        str(EXAMPLE / "basic-evidence-bundle.json"),
        "--strict",
        "--base-dir",
        str(EXAMPLE),
        "--report-out",
        str(report_out),
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    report = json.loads(report_out.read_text(encoding="utf-8"))
    golden = json.loads((EXPECTED / "validation-report.pass.json").read_text(encoding="utf-8"))
    for key in GOLDEN_KEYS:
        assert report[key] == golden[key], key
