#!/usr/bin/env python3
"""Schema-boundary regression tests for the trace replay runner overlay."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

from jsonschema import Draft202012Validator, FormatChecker

REPO = Path(__file__).resolve().parents[2]
OVERLAY = REPO / "tests" / "replay" / "overlays" / "replay_run.py"
TRACE_SCHEMA = (
    REPO
    / "specs"
    / "evidence"
    / "v0.2"
    / "schemas"
    / "trace-replay-cert.schema.json"
)


def _inputs(tmp_path: Path) -> tuple[Path, Path]:
    trace = tmp_path / "trace.json"
    fixtures = tmp_path / "fixtures"
    fixtures.mkdir()
    trace.write_text(
        json.dumps(
            {
                "metadata": {"version": "1.0.0"},
                "events": [
                    {
                        "id": "event-1",
                        "type": "function_call",
                        "payload": {"function": "f"},
                    }
                ],
            }
        ),
        encoding="utf-8",
    )
    (fixtures / "env.json").write_text(
        json.dumps(
            {
                "locale": "C.UTF-8",
                "timezone": "UTC",
                "seed": 1,
                "versions": {"python": "3.11"},
            }
        ),
        encoding="utf-8",
    )
    return trace, fixtures


def _run(tmp_path: Path, env: dict[str, str]) -> tuple[subprocess.CompletedProcess[str], Path]:
    trace, fixtures = _inputs(tmp_path)
    cert_out = tmp_path / "replay.cert.json"
    proc = subprocess.run(
        [
            sys.executable,
            str(OVERLAY),
            "--trace",
            str(trace),
            "--fixtures",
            str(fixtures),
            "--cert-out",
            str(cert_out),
        ],
        cwd=REPO,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    return proc, cert_out


def test_runtime_schema_environment_cannot_hijack_trace_schema(tmp_path: Path) -> None:
    runtime_shape = tmp_path / "runtime.schema.json"
    runtime_shape.write_text(
        json.dumps({"type": "object", "required": ["bundle_id"]}),
        encoding="utf-8",
    )
    env = os.environ.copy()
    env.pop("TRACE_REPLAY_SCHEMA_PATH", None)
    env["TRACE_REPLAY_SCHEMA_REQUIRED"] = "1"
    env["CERT_V1_SCHEMA_PATH"] = str(runtime_shape)
    env["CERT_V1_SCHEMA_REQUIRED"] = "1"

    proc, cert_out = _run(tmp_path, env)
    assert proc.returncode == 0, proc.stderr + proc.stdout
    cert = json.loads(cert_out.read_text(encoding="utf-8"))
    schema = json.loads(TRACE_SCHEMA.read_text(encoding="utf-8"))
    Draft202012Validator(schema, format_checker=FormatChecker()).validate(cert)
    assert "specs/evidence/v0.2/schemas/trace-replay-cert.schema.json" in proc.stdout


def test_explicit_missing_trace_schema_fails_closed(tmp_path: Path) -> None:
    env = os.environ.copy()
    env["TRACE_REPLAY_SCHEMA_PATH"] = str(tmp_path / "missing.schema.json")
    env["TRACE_REPLAY_SCHEMA_REQUIRED"] = "1"

    proc, cert_out = _run(tmp_path, env)
    assert proc.returncode != 0
    assert not cert_out.exists()
    assert "Configured trace replay schema unavailable" in proc.stderr
