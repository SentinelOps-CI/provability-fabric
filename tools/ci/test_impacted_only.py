#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Proof test for P14: build-impacted path must not use "not yet implemented".

import subprocess
import sys
from pathlib import Path


def test_build_impacted_requires_output_dir():
    """--build-impacted without --output-dir exits non-zero (no placeholder message)."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    if not script.exists():
        raise SystemExit("impacted_only.py not found")
    result = subprocess.run(
        [sys.executable, str(script), "--build-impacted"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=10,
    )
    assert result.returncode != 0
    assert "not yet implemented" not in (result.stdout + result.stderr)


def test_impacted_only_help():
    """--help works and script is importable."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=5,
    )
    assert result.returncode == 0
    assert "build-impacted" in result.stdout or "output-dir" in result.stdout
