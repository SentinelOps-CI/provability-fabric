#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Non-vacuous forensic replay tests: identical fixture except one digest."""
from __future__ import annotations

import json
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
PASS = REPO / "examples" / "forensic-replay-basic" / "basic-evidence-bundle.json"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def replay(pf_bin: Path, bundle: Path) -> tuple[int, dict]:
    proc = subprocess.run(
        [str(pf_bin), "evidence", "replay", "--bundle", str(bundle),
         "--base-dir", str(PASS.parent), "--json"],
        cwd=REPO, text=True, capture_output=True, timeout=60,
    )
    try:
        report = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        pytest.fail(f"expected structured replay result: {exc}: {proc.stdout} {proc.stderr}")
    return proc.returncode, report


def test_forensic_pass_case(pf_bin: Path) -> None:
    code, report = replay(pf_bin, PASS)
    assert code == 0, report
    assert report["status"] == report["static_status"] == "pass", report
    assert report["trace_found"] is True and not report["errors"], report


def test_forensic_tamper_case(pf_bin: Path, tmp_path: Path) -> None:
    code, report = replay(pf_bin, PASS)
    assert code == 0 and report["status"] == "pass" and report["trace_found"], report
    bundle = json.loads(PASS.read_text(encoding="utf-8"))
    digest = bundle["bundle_digest"]
    assert digest.startswith("sha256:") and len(digest) == 71
    bundle["bundle_digest"] = digest[:-1] + ("0" if digest[-1] != "0" else "1")
    target = tmp_path / "tampered.json"
    target.write_text(json.dumps(bundle), encoding="utf-8")
    code, report = replay(pf_bin, target)
    assert code != 0, report
    assert report["status"] == report["static_status"] == "fail", report
    assert len(report["errors"]) == 1, report
    assert report["errors"][0].startswith("bundle_digest mismatch:"), report
