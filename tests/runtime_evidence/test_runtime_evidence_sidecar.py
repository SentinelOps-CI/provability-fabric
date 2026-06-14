#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Live sidecar binding integration (Linux CI + CERT-V1 schema gate).

Skipped on Windows local runs only. CI fails if CERT-V1 submodule is missing.
"""

from __future__ import annotations

import os
import platform
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
CERT_SCHEMA = REPO / "external" / "CERT-V1" / "schema" / "cert-v1.schema.json"


def _require_cert_schema() -> None:
    if CERT_SCHEMA.is_file():
        return
    msg = "CERT-V1 schema missing at external/CERT-V1 — run: make submodules"
    if os.environ.get("CI"):
        pytest.fail(msg)
    pytest.skip(msg)


@pytest.mark.skipif(platform.system() == "Windows", reason="live sidecar test runs on Linux CI")
def test_sidecar_write_cert_with_binding_emits_jsonl() -> None:
    _require_cert_schema()
    proc = subprocess.run(
        [
            "cargo",
            "test",
            "-p",
            "sidecar-watcher",
            "write_cert_with_binding_emits_binding_jsonl",
            "--",
            "--nocapture",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout


@pytest.mark.skipif(platform.system() == "Windows", reason="live sidecar test runs on Linux CI")
def test_emit_evidence_through_permit_enforcement() -> None:
    _require_cert_schema()
    proc = subprocess.run(
        [
            "cargo",
            "test",
            "-p",
            "sidecar-watcher",
            "emit_evidence_binding_through_permit_enforcement",
            "--",
            "--nocapture",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
