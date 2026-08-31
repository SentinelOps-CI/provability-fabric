#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Schema checks for TRACE-REPLAY-KIT trace_replay certificates."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "tools" / "cert-validate"))
from format_check import (  # noqa: E402
    FormatCheckUnavailable,
    compile_trace_replay_validator,
    require_date_time_format_checker,
)

SCHEMA_PATH = (
    REPO
    / "specs"
    / "evidence"
    / "v0.2"
    / "schemas"
    / "trace-replay-cert.schema.json"
)
REPLAY_OUT = REPO / "specs" / "evidence" / "v0.2" / "examples" / "valid" / "replay-out"


def _validator() -> Draft202012Validator:
    schema = json.loads(SCHEMA_PATH.read_text(encoding="utf-8"))
    return compile_trace_replay_validator(schema)


@pytest.mark.parametrize("name", ["replay.cert.json", "replay2.cert.json"])
def test_expected_trace_replay_certificates_validate(name: str) -> None:
    cert = json.loads((REPLAY_OUT / name).read_text(encoding="utf-8"))
    _validator().validate(cert)


def test_trace_replay_certificate_schema_rejects_missing_summary() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert.pop("summary")
    errors = list(_validator().iter_errors(cert))
    assert errors


def test_trace_replay_certificate_schema_rejects_wrong_cert_type() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert["cert_type"] = "runtime_cert"
    errors = list(_validator().iter_errors(cert))
    assert errors


def test_trace_replay_certificate_schema_rejects_bad_signature_hash_shape() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert["signature"]["hash"] = "not-a-sha256-digest"
    errors = list(_validator().iter_errors(cert))
    assert errors


def test_trace_replay_certificate_schema_rejects_invalid_timestamp() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert["timestamp"] = "not-a-timestamp"
    errors = list(_validator().iter_errors(cert))
    assert errors


def test_date_time_format_checker_fails_closed_when_backend_missing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        "format_check.importlib.util.find_spec", lambda name: None
    )
    with pytest.raises(FormatCheckUnavailable, match="rfc3339-validator"):
        require_date_time_format_checker()


def test_trace_replay_certificate_schema_rejects_result_without_event_id() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert["results"][0].pop("event_id")
    errors = list(_validator().iter_errors(cert))
    assert errors


def test_trace_replay_certificate_schema_rejects_unknown_result_status() -> None:
    cert = json.loads((REPLAY_OUT / "replay.cert.json").read_text(encoding="utf-8"))
    cert["results"][0]["status"] = "unknown"
    errors = list(_validator().iter_errors(cert))
    assert errors
