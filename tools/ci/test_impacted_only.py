#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Proof tests for P14 / F12: build-impacted path writes real artifacts.

import json
import subprocess
import sys
import tempfile
from pathlib import Path


def test_build_impacted_requires_output_dir():
    """--build-impacted without --output-dir exits non-zero."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    result = subprocess.run(
        [sys.executable, str(script), "--build-impacted"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=30,
    )
    assert result.returncode != 0
    assert "output-dir" in (result.stdout + result.stderr).lower()


def test_build_impacted_writes_plan():
    """--build-impacted emits build_plan.json and build_impacted.sh."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    with tempfile.TemporaryDirectory() as tmp:
        out = Path(tmp)
        result = subprocess.run(
            [
                sys.executable,
                str(script),
                "--build-impacted",
                "--output-dir",
                str(out),
                "--workspace",
                str(root),
            ],
            capture_output=True,
            text=True,
            cwd=root,
            timeout=120,
        )
        assert result.returncode == 0, result.stderr
        plan = out / "build_plan.json"
        shell = out / "build_impacted.sh"
        assert plan.is_file()
        assert shell.is_file()
        data = json.loads(plan.read_text(encoding="utf-8"))
        assert data["build_type"] == "impacted_only"
        assert "build_steps" in data


def test_impacted_only_help():
    """--help works."""
    root = Path(__file__).resolve().parents[2]
    script = root / "tools" / "ci" / "impacted_only.py"
    result = subprocess.run(
        [sys.executable, str(script), "--help"],
        capture_output=True,
        text=True,
        cwd=root,
        timeout=10,
    )
    assert result.returncode == 0
    assert "build-impacted" in result.stdout or "output-dir" in result.stdout
