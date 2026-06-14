#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Pytest discoverability shim for core/evidence pack tests (Go-native)."""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
EVIDENCE_DIR = REPO / "core" / "evidence"


def test_pack_go_tests() -> None:
    proc = subprocess.run(
        ["go", "test", "./...", "-run", "TestPack|TestBundleDigest|TestBundleToMap|TestCanonicalJSON|TestFileDigest"],
        cwd=EVIDENCE_DIR,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
