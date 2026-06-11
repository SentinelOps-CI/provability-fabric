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


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def run_pf(pf_bin: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(pf_bin), *args], cwd=REPO, text=True, capture_output=True)


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
