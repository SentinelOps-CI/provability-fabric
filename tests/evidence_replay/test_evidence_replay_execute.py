#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Deep replay execute tests (requires TRACE-REPLAY-KIT submodule)."""

from __future__ import annotations

import json
import platform
import subprocess
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, FormatChecker

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
BUNDLE = REPO / "specs" / "evidence" / "v0.2" / "examples" / "valid" / "deep-replay-bundle.json"
KIT_RUNNER = REPO / "external" / "TRACE-REPLAY-KIT" / "runner" / "replay_run.py"
TRACE_REPLAY_SCHEMA = (
    REPO
    / "specs"
    / "evidence"
    / "v0.2"
    / "schemas"
    / "trace-replay-cert.schema.json"
)


def _pf_bin() -> Path:
    for candidate in (PF, REPO / "core" / "cli" / "pf" / "pf.exe"):
        if candidate.exists():
            return candidate
    subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    return _pf_bin()


@pytest.mark.skipif(platform.system() == "Windows", reason="KIT execute replay runs on Linux CI")
@pytest.mark.skipif(not KIT_RUNNER.is_file(), reason="TRACE-REPLAY-KIT missing (make submodules)")
def test_evidence_replay_execute_low_view(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "replay-report.json"
    proc = subprocess.run(
        [
            str(pf_bin),
            "evidence",
            "replay",
            "--bundle",
            str(BUNDLE),
            "--base-dir",
            str(BUNDLE.parent),
            "--execute",
            "--low-view",
            "--out-dir",
            str(tmp_path / "kit-out"),
            "--out",
            str(out),
            "--json",
        ],
        cwd=REPO,
        text=True,
        capture_output=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stderr + proc.stdout
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "pass"
    assert report.get("execute_status") == "pass"
    assert report.get("low_view_result") == "pass"
    assert report.get("replay_cert_validation") == "pass"
    assert report.get("replay_cert_schema") == (
        "specs/evidence/v0.2/schemas/trace-replay-cert.schema.json"
    )
    assert report.get("replay_artifacts") == [
        "replay.cert.json",
        "replay2.cert.json",
    ]

    schema = json.loads(TRACE_REPLAY_SCHEMA.read_text(encoding="utf-8"))
    validator = Draft202012Validator(schema, format_checker=FormatChecker())

    bundle = json.loads(BUNDLE.read_text(encoding="utf-8"))
    bundle_base = BUNDLE.parent.resolve()
    trace_path = (bundle_base / bundle["replay_context"]["kit_trace_path"]).resolve()
    fixtures_path = (bundle_base / bundle["replay_context"]["fixtures_path"]).resolve()
    assert trace_path.is_relative_to(bundle_base)
    assert fixtures_path.is_relative_to(bundle_base)
    env_path = (fixtures_path / "env.json").resolve()
    assert env_path.is_relative_to(fixtures_path)
    trace = json.loads(trace_path.read_text(encoding="utf-8"))
    environment = json.loads(env_path.read_text(encoding="utf-8"))
    expected_event_ids = [event["id"] for event in trace.get("events", [])]

    for name in report["replay_artifacts"]:
        cert = json.loads((tmp_path / "kit-out" / name).read_text(encoding="utf-8"))
        validator.validate(cert)
        assert cert["trace_metadata"] == trace.get("metadata", {})
        assert cert["environment"] == environment
        assert [result["event_id"] for result in cert["results"]] == expected_event_ids
        statuses = [result["status"] for result in cert["results"]]
        assert statuses == ["success"] * len(expected_event_ids)
        assert cert["summary"] == {
            "total_events": len(expected_event_ids),
            "successful_events": len(expected_event_ids),
            "failed_events": 0,
        }
