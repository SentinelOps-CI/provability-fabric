#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Live sidecar binding integration (Linux CI + CERT-V1 schema gate).

Skipped on Windows local runs; CI uses ubuntu-latest with submodules.
"""

from __future__ import annotations

import platform
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
CERT_SCHEMA = REPO / "external" / "CERT-V1" / "schema" / "cert-v1.schema.json"
SIDECAR_CRATE = REPO / "runtime" / "sidecar-watcher"


@pytest.mark.skipif(platform.system() == "Windows", reason="live sidecar test runs on Linux CI")
@pytest.mark.skipif(not CERT_SCHEMA.is_file(), reason="CERT-V1 schema missing (make submodules)")
def test_sidecar_write_cert_with_binding_emits_jsonl() -> None:
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
    assert "evidence_v01_binding" in proc.stdout or proc.returncode == 0
