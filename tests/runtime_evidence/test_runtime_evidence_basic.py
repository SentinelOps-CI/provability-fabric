#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Runtime evidence basic scenario checks."""

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


def test_runtime_bundle_validates(pf_bin: Path) -> None:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "validate", str(BUNDLE), "--strict"],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout


def test_binding_event_shape() -> None:
    event = json.loads(BINDING.read_text(encoding="utf-8"))
    assert event["event_type"] == "evidence_v01_binding"
    assert event["schema_version"] == "0.1"
    assert "cert-v1" in event["artifact_digests"]
    assert event["evidence_bundle_ref"].endswith("basic-evidence-bundle.json")


def test_runtime_tampered_bundle_fails(pf_bin: Path, tmp_path: Path) -> None:
    tampered = json.loads(BUNDLE.read_text(encoding="utf-8"))
    tampered["bundle_digest"] = "sha256:" + "f" * 64
    path = tmp_path / "tampered.json"
    path.write_text(json.dumps(tampered, indent=2) + "\n", encoding="utf-8")
    proc = subprocess.run(
        [str(pf_bin), "evidence", "validate", str(path), "--strict", "--base-dir", str(EXAMPLE)],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode != 0
