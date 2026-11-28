#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Strict validation tests for pf evidence validate."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
PF = REPO / "core" / "cli" / "pf" / "pf"
VALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "valid" / "basic-evidence-bundle.json"
INVALID = REPO / "specs" / "evidence" / "v0.1" / "examples" / "invalid"
SCHEMAS = REPO / "specs" / "evidence" / "v0.1" / "schemas"


@pytest.fixture(scope="module")
def pf_bin() -> Path:
    if not PF.exists():
        subprocess.run(["go", "build", "-o", "pf", "."], cwd=REPO / "core" / "cli" / "pf", check=True)
    return PF


def run_pf(pf_bin: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run([str(pf_bin), *args], cwd=REPO, text=True, capture_output=True)


def test_validate_valid_bundle_strict(pf_bin: Path) -> None:
    proc = run_pf(pf_bin, "evidence", "validate", str(VALID), "--strict")
    assert proc.returncode == 0, proc.stderr + proc.stdout


def test_validate_missing_artifact_fails(pf_bin: Path) -> None:
    proc = run_pf(pf_bin, "evidence", "validate", str(INVALID / "missing-artifacts.json"), "--strict")
    assert proc.returncode != 0


def test_validate_tampered_bundle_digest_fails(pf_bin: Path) -> None:
    """Digest mismatch is not a schema error — bundle shape is valid but digest check fails."""
    proc = run_pf(pf_bin, "evidence", "validate", str(INVALID / "bad-bundle-digest.json"), "--strict")
    assert proc.returncode != 0
    assert "digest" in (proc.stderr + proc.stdout).lower()


def test_validate_bad_bundle_digest_report(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "report.json"
    proc = run_pf(
        pf_bin,
        "evidence",
        "validate",
        str(INVALID / "bad-bundle-digest.json"),
        "--strict",
        "--report-out",
        str(out),
    )
    assert proc.returncode != 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "fail"
    assert report["errors"]


def test_validate_invalid_json_fails(pf_bin: Path, tmp_path: Path) -> None:
    bad = tmp_path / "not-json.json"
    bad.write_text("{ not valid json\n", encoding="utf-8")
    out = tmp_path / "report.json"
    proc = run_pf(pf_bin, "evidence", "validate", str(bad), "--strict", "--report-out", str(out))
    assert proc.returncode != 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "fail"
    combined = " ".join(report["errors"]).lower()
    assert "json" in combined or "parse" in combined or "syntax" in combined


def test_validate_missing_schema_fails_closed(pf_bin: Path, tmp_path: Path) -> None:
    empty = tmp_path / "empty-base"
    empty.mkdir()
    shutil.copy(VALID, empty / "bundle.json")
    proc = run_pf(
        pf_bin,
        "evidence",
        "validate",
        str(empty / "bundle.json"),
        "--strict",
        "--base-dir",
        str(empty),
    )
    assert proc.returncode != 0
    assert "schema" in (proc.stderr + proc.stdout).lower()


def test_validate_emits_report(pf_bin: Path, tmp_path: Path) -> None:
    out = tmp_path / "report.json"
    proc = run_pf(pf_bin, "evidence", "validate", str(VALID), "--strict", "--report-out", str(out))
    assert proc.returncode == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "pass"


def test_attestation_reference_profile(pf_bin: Path, tmp_path: Path) -> None:
    """Repack adversarial bytes: a valid outer hash must not excuse a false nested reference."""
    import hashlib

    shutil.copytree(VALID.parent / "artifacts", tmp_path / "artifacts")
    shutil.copy(VALID.parent / "manifest.json", tmp_path / "manifest.json")
    manifest = tmp_path / "manifest.json"
    bundle = tmp_path / "bundle.json"
    att_path = tmp_path / "artifacts" / "attestation.json"
    att = json.loads(att_path.read_text(encoding="utf-8"))
    proof = tmp_path / att["signed_claim_ref"]["path"]
    att["signed_claim_ref"]["digest"] = "sha256:" + hashlib.sha256(proof.read_bytes()).hexdigest()
    att_path.write_text(json.dumps(att), encoding="utf-8")

    def pack() -> None:
        proc = run_pf(pf_bin, "evidence", "bundle", "pack", "--manifest", str(manifest), "--out", str(bundle))
        assert proc.returncode == 0, proc.stderr + proc.stdout

    pack()
    proc = run_pf(pf_bin, "evidence", "validate", str(bundle), "--strict", "--require-attestation-references", "--json")
    assert proc.returncode == 0, proc.stderr + proc.stdout
    report = json.loads(proc.stdout)
    assert report["status"] == "pass"
    assert any("signatures and claim validity not verified" in item for item in report["warnings"])

    att["signed_claim_ref"]["digest"] = "sha256:" + "0" * 64
    att_path.write_text(json.dumps(att), encoding="utf-8")
    pack()
    structural = run_pf(pf_bin, "evidence", "validate", str(bundle), "--strict")
    assert structural.returncode == 0, structural.stderr + structural.stdout
    rejected = run_pf(pf_bin, "evidence", "validate", str(bundle), "--strict", "--require-attestation-references")
    assert rejected.returncode != 0
    assert "signed_claim_ref" in rejected.stderr + rejected.stdout
