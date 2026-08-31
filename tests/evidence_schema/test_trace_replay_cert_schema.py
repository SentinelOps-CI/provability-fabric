#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Schema checks for TRACE-REPLAY-KIT trace_replay certificates."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
from jsonschema import Draft202012Validator, FormatChecker

REPO = Path(__file__).resolve().parents[2]
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
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema, format_checker=FormatChecker())


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
