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


def test_independent_execution_attestation_signature(pf_bin: Path, tmp_path: Path) -> None:
    """OpenSSL creates the signature independently; repack every adversarial mutation."""
    import base64
    import hashlib
    import struct

    artifacts = tmp_path / "artifacts"
    artifacts.mkdir()
    trace = artifacts / "trace.json"
    shutil.copy(VALID.parent / "artifacts" / "execution-trace.json", trace)
    key, other, public = (tmp_path / n for n in ("key.pem", "other.pem", "pub.der"))

    def openssl(*args: str) -> bytes:
        return subprocess.run(["openssl", *args], capture_output=True, check=True, timeout=15).stdout

    for private in (key, other):
        openssl("genpkey", "-algorithm", "Ed25519", "-out", str(private))
    openssl("pkey", "-in", str(key), "-pubout", "-outform", "DER", "-out", str(public))
    der = public.read_bytes()
    assert der[:12].hex() == "302a300506032b6570032100" and len(der) == 44
    digest = "sha256:" + hashlib.sha256(trace.read_bytes()).hexdigest()
    ref = {"role":"execution-trace", "path":"artifacts/trace.json",
           "media_type":"application/vnd.provability-fabric.evidence.execution-trace+json", "digest":digest}
    att = {"schema_version":"0.1", "attestation_id":"independent-1",
           "attestor":"test-issuer", "signed_claim_ref":ref}
    att_path = artifacts / "attestation.json"
    manifest_path, bundle_path, trust_path = (tmp_path / n for n in ("manifest.json", "bundle.json", "trust.json"))
    manifest = {"schema_version":"0.1", "bundle_id":"independent-run", "producer":"fixture",
                "created_at":"2025-01-01T00:00:00Z", "artifacts":[
                {"role":ref["role"],"path":ref["path"],"media_type":ref["media_type"]},
                {"role":"attestation","path":"artifacts/attestation.json"}]}
    trust = {"profile":"ed25519-execution-v1", "expected_bundle_id":"independent-run",
             "expected_trace_digest":digest, "attestor":"test-issuer",
             "public_key_base64":base64.b64encode(der[12:]).decode()}

    def sign(private: Path) -> str:
        fields = [manifest["schema_version"], manifest["bundle_id"], att["schema_version"],
                  att["attestation_id"], att["attestor"], ref["role"], ref["path"],
                  ref["media_type"], ref["digest"], ""]
        message = b"provability-fabric/execution-attestation/v1\\x00" + b"".join(
            struct.pack(">Q", len(field.encode())) + field.encode() for field in fields)
        msg = tmp_path / "message"
        msg.write_bytes(message)
        return "ed25519-execution-v1:" + base64.b64encode(
            openssl("pkeyutl", "-sign", "-inkey", str(private), "-rawin", "-in", str(msg))).decode()

    att["signature"] = sign(key)
    original_signature = att["signature"]

    def verify(expected: bool, reason: str = "") -> None:
        att_path.write_text(json.dumps(att), encoding="utf-8")
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        trust_path.write_text(json.dumps(trust), encoding="utf-8")
        packed = run_pf(pf_bin, "evidence", "bundle", "pack", "--manifest", str(manifest_path), "--out", str(bundle_path))
        assert packed.returncode == 0, packed.stdout + packed.stderr
        result = run_pf(pf_bin, "evidence", "validate", str(bundle_path), "--strict",
                        "--execution-attestation-trust", str(trust_path), "--json")
        assert (result.returncode == 0) == expected, result.stdout + result.stderr
        report = json.loads(result.stdout)
        assert report["status"] == ("pass" if expected else "fail")
        if expected:
            assert any("execution authenticity" in item for item in report["warnings"])
        else:
            assert reason in " ".join(report["errors"]), report

    verify(True)
    att["signature"] = sign(other)
    verify(False, "signature verification failed")
    att["signature"] = "demo-signature-placeholder"
    verify(False, "unsupported signature profile")
    att["signature"] = original_signature
    att["attestation_id"] = "different-id"
    verify(False, "signature verification failed")
    att["attestation_id"] = "independent-1"
    trust["attestor"] = "different-issuer"
    verify(False, "selected attestor and trace")
    trust["attestor"] = "test-issuer"
    trust["expected_bundle_id"] = "other-run"
    verify(False, "unexpected execution bundle identity")
    trust["expected_bundle_id"] = "independent-run"
    trust["expected_trace_digest"] = "sha256:" + "0" * 64
    verify(False, "externally identified execution trace")
    trust["expected_trace_digest"] = digest
    verify(True)
