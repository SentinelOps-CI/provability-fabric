#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Evidence trace import CLI tests."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import jsonschema
import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
KIT_TRACE = REPO / "tests" / "replay" / "bundles" / "simple" / "trace.json"
SCHEMA = REPO / "specs" / "evidence" / "v0.1" / "schemas" / "execution-trace.schema.json"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists() and not (REPO / "core" / "cli" / "pf" / "pf.exe").exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    for candidate in (PF, REPO / "core" / "cli" / "pf" / "pf.exe"):
        if candidate.exists():
            return candidate
    raise RuntimeError("pf binary not found")


def test_trace_import_validates_strict(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "execution-trace.json"
    proc = subprocess.run(
        [
            str(pf_bin),
            "evidence",
            "trace",
            "import",
            "--kit-trace",
            str(KIT_TRACE),
            "--out",
            str(out),
            "--trace-id",
            "pytest-import",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    data = json.loads(out.read_text(encoding="utf-8"))
    schema = json.loads(SCHEMA.read_text(encoding="utf-8"))
    jsonschema.validate(data, schema)
    assert data["trace_id"] == "pytest-import"
    assert len(data["events"]) >= 1
