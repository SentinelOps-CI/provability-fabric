#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Schema validation tests for Evidence v0.1 fixtures."""

from __future__ import annotations

import json
from pathlib import Path

import jsonschema
import pytest

REPO = Path(__file__).resolve().parents[2]
SCHEMA_DIR = REPO / "specs" / "evidence" / "v0.1" / "schemas"
VALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "valid"
INVALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "invalid"


def load_schema(name: str) -> dict:
    return json.loads((SCHEMA_DIR / name).read_text(encoding="utf-8"))


@pytest.mark.parametrize(
    "artifact,schema_name",
    [
        ("artifacts/claim.json", "claim.schema.json"),
        ("artifacts/proof.json", "proof.schema.json"),
        ("artifacts/attestation.json", "attestation.schema.json"),
        ("artifacts/execution-trace.json", "execution-trace.schema.json"),
        ("basic-evidence-bundle.json", "evidence-bundle.schema.json"),
        ("basic-validation-report.json", "validation-report.schema.json"),
    ],
)
def test_valid_fixtures(artifact: str, schema_name: str) -> None:
    schema = load_schema(schema_name)
    data = json.loads((VALID / artifact).read_text(encoding="utf-8"))
    jsonschema.validate(instance=data, schema=schema)


@pytest.mark.parametrize(
    "fixture,schema_name",
    [
        ("bad-claim.json", "claim.schema.json"),
        ("bad-proof.json", "proof.schema.json"),
        ("bad-attestation.json", "attestation.schema.json"),
        ("bad-execution-trace.json", "execution-trace.schema.json"),
        ("bad-evidence-bundle.json", "evidence-bundle.schema.json"),
        ("bad-validation-report.json", "validation-report.schema.json"),
    ],
)
def test_invalid_fixtures_rejected(fixture: str, schema_name: str) -> None:
    schema = load_schema(schema_name)
    data = json.loads((INVALID / fixture).read_text(encoding="utf-8"))
    with pytest.raises(jsonschema.ValidationError):
        jsonschema.validate(instance=data, schema=schema)


def test_bundle_has_digest_prefix() -> None:
    bundle = json.loads((VALID / "basic-evidence-bundle.json").read_text(encoding="utf-8"))
    assert bundle["bundle_digest"].startswith("sha256:")
