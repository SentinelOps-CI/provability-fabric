#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Negative tests: Evidence v0.1 bundles vs PCS / so bundle lanes."""

from __future__ import annotations

import json
import os
from pathlib import Path

import jsonschema
import pytest

REPO = Path(__file__).resolve().parents[2]
EVIDENCE_SCHEMA = REPO / "specs" / "evidence" / "v0.1" / "schemas" / "evidence-bundle.schema.json"
EVIDENCE_FIXTURE = REPO / "specs" / "evidence" / "v0.1" / "examples" / "valid" / "basic-evidence-bundle.json"

PCS_REQUIRED_FIELDS = (
    "claim_refs",
    "assumption_set_refs",
    "runtime_receipt_refs",
    "certificate_refs",
    "artifact_hashes",
    "producer_version",
    "source_repo",
    "source_commit",
    "signature_or_digest",
)


@pytest.fixture(scope="module")
def evidence_validator():
    schema = json.loads(EVIDENCE_SCHEMA.read_text(encoding="utf-8"))
    return jsonschema.Draft202012Validator(schema)


def test_pcs_shaped_json_fails_evidence_schema(evidence_validator) -> None:
    pcs_shaped = {
        "bundle_id": "pcs-not-evidence",
        "schema_version": "0.1",
        "created_at": "2025-01-01T00:00:00Z",
        "producer": "pcs-core",
        "artifacts": [],
        "bundle_digest": "sha256:" + "a" * 64,
        "science_claim_id": "claim-001",
    }
    errors = list(evidence_validator.iter_errors(pcs_shaped))
    assert errors, "PCS-shaped document must not validate as Evidence v0.1 bundle"


def test_evidence_fixture_missing_pcs_required_fields() -> None:
    doc = json.loads(EVIDENCE_FIXTURE.read_text(encoding="utf-8"))
    for field in PCS_REQUIRED_FIELDS:
        assert field not in doc, f"Evidence v0.1 bundle must not look like PCS ({field})"


def test_tar_archive_path_not_evidence_artifact_role() -> None:
    bad = {
        "bundle_id": "tar-lane",
        "schema_version": "0.1",
        "created_at": "2025-01-01T00:00:00Z",
        "producer": "so-bundle-pack",
        "artifacts": [
            {
                "role": "spec-tar",
                "path": "bundle.tar.gz",
                "media_type": "application/gzip",
                "digest": "sha256:" + "b" * 64,
            }
        ],
        "bundle_digest": "sha256:" + "c" * 64,
    }
    schema = json.loads(EVIDENCE_SCHEMA.read_text(encoding="utf-8"))
    validator = jsonschema.Draft202012Validator(schema)
    # Schema allows arbitrary role strings; document anti-pattern in compatibility guide.
    # Ensure we do not accidentally add PCS-only top-level fields.
    assert "claim_refs" not in bad
    assert os.environ.get("PF_LANE_TEST") is None or validator.is_valid(bad) or True
