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


def _execute_exact(target: list[str], name: str, marker: str) -> None:
    _require_cert_schema()
    env = dict(os.environ, CERT_V1_SCHEMA=str(CERT_SCHEMA.resolve(strict=True)))
    proc = subprocess.run(
        ["cargo", "test", "--locked", "-p", "sidecar-watcher", *target,
         name, "--", "--ignored", "--exact", "--nocapture", "--test-threads=1"],
        cwd=REPO, env=env, text=True, capture_output=True, timeout=600,
    )
    output = proc.stdout + proc.stderr
    assert proc.returncode == 0, output
    assert "running 1 test" in output, output
    assert "1 passed; 0 failed; 0 ignored" in output, output
    assert marker in output, output


@pytest.mark.skipif(platform.system() == "Windows", reason="live sidecar test runs on Linux CI")
def test_sidecar_write_cert_with_binding_emits_jsonl() -> None:
    _execute_exact(["--lib"], "cert_v1::tests::write_cert_with_binding_emits_binding_jsonl",
                   "PASS: emitted certificate digest matches binding")


@pytest.mark.skipif(platform.system() == "Windows", reason="live sidecar test runs on Linux CI")
def test_emit_evidence_through_permit_enforcement() -> None:
    _execute_exact(["--test", "emit_evidence_tests"],
                   "emit_evidence_binding_through_permit_enforcement",
                   "PASS: permit emission digest matches binding")
