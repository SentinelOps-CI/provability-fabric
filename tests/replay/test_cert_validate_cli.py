#!/usr/bin/env python3
"""Fail-closed CLI regression tests for certificate validation."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
TOOL = REPO / "tools" / "cert-validate" / "validate.py"


def _run(*args: str, cwd: Path = REPO) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, str(TOOL), *args],
        cwd=cwd,
        text=True,
        capture_output=True,
        check=False,
    )


def _trace_cert(path: Path, timestamp: str = "2026-01-01T00:00:00Z") -> Path:
    cert = {
        "$schema": "https://provability-fabric.org/schemas/evidence/v0.2/trace-replay-cert.schema.json",
        "cert_type": "trace_replay",
        "version": "1.0.0",
        "timestamp": timestamp,
        "replay_id": "0123456789abcdef",
        "trace_metadata": {},
        "environment": {
            "locale": "C.UTF-8",
            "timezone": "UTC",
            "seed": 1,
            "versions": {"python": "3.11"},
        },
        "results": [],
        "summary": {"total_events": 0, "successful_events": 0, "failed_events": 0},
        "signature": {"algorithm": "sha256", "hash": "a" * 64},
    }
    path.write_text(json.dumps(cert), encoding="utf-8")
    return path


def test_trace_replay_does_not_require_runtime_schema(tmp_path: Path) -> None:
    cert = _trace_cert(tmp_path / "trace.cert.json")
    missing = tmp_path / "missing-runtime-schema.json"
    proc = _run("--schema", str(missing), str(cert), cwd=tmp_path)
    assert proc.returncode == 0, proc.stdout + proc.stderr


def test_invalid_trace_replay_is_validation_failure(tmp_path: Path) -> None:
    cert = _trace_cert(tmp_path / "trace.cert.json", timestamp="not-a-timestamp")
    proc = _run("--schema", str(tmp_path / "missing.json"), str(cert))
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "date-time" in proc.stdout


def test_missing_explicit_file_is_operational_error(tmp_path: Path) -> None:
    proc = _run(str(tmp_path / "missing.cert.json"))
    assert proc.returncode == 2, proc.stdout + proc.stderr


def test_empty_glob_is_operational_error(tmp_path: Path) -> None:
    proc = _run(str(tmp_path / "*.cert.json"))
    assert proc.returncode == 2, proc.stdout + proc.stderr


def test_runtime_certificate_missing_schema_is_operational_error(tmp_path: Path) -> None:
    cert = tmp_path / "runtime.cert.json"
    cert.write_text(json.dumps({"sig": "example"}), encoding="utf-8")
    proc = _run("--schema", str(tmp_path / "missing.json"), str(cert))
    assert proc.returncode == 2, proc.stdout + proc.stderr


def test_runtime_schema_rejection_is_validation_failure(tmp_path: Path) -> None:
    schema = tmp_path / "runtime.schema.json"
    schema.write_text(
        json.dumps({"type": "object", "required": ["sig"]}), encoding="utf-8"
    )
    cert = tmp_path / "runtime.cert.json"
    cert.write_text(json.dumps({"bundle_id": "x"}), encoding="utf-8")
    proc = _run("--schema", str(schema), str(cert))
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "sig" in proc.stdout


def test_allow_missing_runtime_schema_reports_skip_not_pass(tmp_path: Path) -> None:
    cert = tmp_path / "runtime.cert.json"
    cert.write_text(json.dumps({"sig": "example"}), encoding="utf-8")
    proc = _run(
        "--allow-missing-schema",
        "--schema",
        str(tmp_path / "missing.json"),
        str(cert),
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "Passed: 0" in proc.stdout
    assert "Skipped: 1" in proc.stdout
    assert "explicit skip" in proc.stdout
    assert "All files validated successfully" not in proc.stdout


def test_non_utf8_certificate_is_operational_error(tmp_path: Path) -> None:
    cert = tmp_path / "non-utf8.cert.json"
    cert.write_bytes(b"\xff\xfe\x00")
    proc = _run(str(cert))
    assert proc.returncode == 2, proc.stdout + proc.stderr
    assert "file error" in proc.stdout
    assert "Invalid JSON" not in proc.stdout


def test_trace_replay_result_missing_event_id_is_validation_failure(tmp_path: Path) -> None:
    cert_path = _trace_cert(tmp_path / "trace.cert.json")
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    cert["results"] = [{"status": "success"}]
    cert["summary"] = {"total_events": 1, "successful_events": 1, "failed_events": 0}
    cert_path.write_text(json.dumps(cert), encoding="utf-8")
    proc = _run(str(cert_path))
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "event_id" in proc.stdout


def test_trace_replay_unknown_result_status_is_validation_failure(tmp_path: Path) -> None:
    cert_path = _trace_cert(tmp_path / "trace.cert.json")
    cert = json.loads(cert_path.read_text(encoding="utf-8"))
    cert["results"] = [{"event_id": "event_001", "status": "unknown"}]
    cert["summary"] = {"total_events": 1, "successful_events": 0, "failed_events": 0}
    cert_path.write_text(json.dumps(cert), encoding="utf-8")
    proc = _run(str(cert_path))
    assert proc.returncode == 1, proc.stdout + proc.stderr
    assert "unknown" in proc.stdout
