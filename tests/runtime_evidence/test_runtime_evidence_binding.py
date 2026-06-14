#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Runtime evidence binding tests."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
EXAMPLE = REPO / "examples" / "runtime-evidence-basic"
BUNDLE = EXAMPLE / "basic-evidence-bundle.json"
BINDING = EXAMPLE / "binding-event.json"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def test_binding_event_shape() -> None:
    data = json.loads(BINDING.read_text(encoding="utf-8"))
    assert data["event_type"] == "evidence_v01_binding"
    assert "artifact_digests" in data


def test_binding_bundle_validates_strict(pf_bin: Path) -> None:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "validate", str(BUNDLE), "--strict", "--base-dir", str(EXAMPLE)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout


def test_binding_refs_resolve_in_bundle(pf_bin: Path) -> None:
    binding = json.loads(BINDING.read_text(encoding="utf-8"))
    bundle = json.loads(BUNDLE.read_text(encoding="utf-8"))
    bundle_ref = binding["evidence_bundle_ref"]
    assert bundle_ref.endswith("basic-evidence-bundle.json")
    roles = {a["role"] for a in bundle["artifacts"]}
    assert "attestation" in roles
    assert "execution-trace" in roles
    proc = subprocess.run(
        [str(pf_bin), "evidence", "validate", str(BUNDLE), "--strict"],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0
