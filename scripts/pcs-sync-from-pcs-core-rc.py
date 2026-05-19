#!/usr/bin/env python3
"""Sync PF labtrust-release fixtures from canonical pcs-core/examples/labtrust-release/."""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys

PF_ARTIFACTS = (
    "science_claim_bundle.certified.json",
    "verification_result.json",
    "signed_science_claim_bundle.json",
)

FORMAL_ARTIFACTS = (
    "proof_obligation.v0.json",
    "lean_check_result.v0.json",
)

PF_PROTOCOL_FROM_RC = (
    ("handoff_to_pf.json", "handoff_to_pf.json"),
    ("handoff_manifest.bundle_to_verifier.v0.json", "handoff_to_pf.json"),
    ("release_manifest.v0.json", "release_manifest.json"),
    ("release_chain_validation_result.v0.json", "release_chain_validation_result.json"),
)

PF_PROTOCOL_ALSO_COPY = (
    ("release_manifest.v0.json", "release_manifest.v0.json"),
)

# PF release-chain segment artifacts (upstream capture pins are pruned from synced manifests).
PF_RELEASE_MANIFEST_ARTIFACTS = frozenset(
    {
        "science_claim_bundle.certified.json",
        "verification_result.json",
        "signed_science_claim_bundle.json",
        "scientific_memory_import_report.json",
    }
)

PF_PROTOCOL_FALLBACK = (
    ("handoff_manifest.valid.json", "handoff_to_pf.json"),
    ("release_manifest.valid.json", "release_manifest.json"),
    ("artifact_registry.valid.json", "artifact_registry.json"),
)


def refresh_handoff_to_pf(pf_release: pathlib.Path) -> None:
    """Align handoff_to_pf.json invariants with the synced certified bundle."""
    certified_path = pf_release / "science_claim_bundle.certified.json"
    handoff_path = pf_release / "handoff_to_pf.json"
    if not certified_path.is_file() or not handoff_path.is_file():
        return
    certified = json.loads(certified_path.read_text(encoding="utf-8"))
    handoff = json.loads(handoff_path.read_text(encoding="utf-8"))
    bundle_hash = sha256_file(certified_path)
    cert_id = certified["certificates"][0]["certificate_id"]
    trace_hash = certified["runtime_receipts"][0]["trace_hash"]
    inv = handoff.setdefault("invariants", {})
    inv["certified_bundle_hash"] = bundle_hash
    inv["certificate_id"] = cert_id
    inv["trace_hash"] = trace_hash
    inp = handoff.setdefault("input_artifacts", {})
    scb = inp.setdefault("science_claim_bundle.certified.json", {})
    if isinstance(scb, dict):
        scb["sha256"] = bundle_hash
    handoff_path.write_text(json.dumps(handoff, indent=2) + "\n", encoding="utf-8")


def prune_pf_release_manifest(pf_release: pathlib.Path) -> None:
    """Keep only PF-segment artifact pins; refresh chain_root from the certified bundle."""
    certified_path = pf_release / "science_claim_bundle.certified.json"
    if not certified_path.is_file():
        return
    certified = json.loads(certified_path.read_text(encoding="utf-8"))
    bundle_hash = sha256_file(certified_path)
    cert_id = certified["certificates"][0]["certificate_id"]
    trace_hash = certified["runtime_receipts"][0]["trace_hash"]
    for name in ("release_manifest.v0.json", "release_manifest.json"):
        path = pf_release / name
        if not path.is_file():
            continue
        manifest = json.loads(path.read_text(encoding="utf-8"))
        manifest["artifacts"] = {
            k: v
            for k, v in manifest.get("artifacts", {}).items()
            if k in PF_RELEASE_MANIFEST_ARTIFACTS
        }
        chain_root = manifest.setdefault("chain_root", {})
        chain_root["certified_bundle_hash"] = bundle_hash
        chain_root["certificate_id"] = cert_id
        chain_root["trace_hash"] = trace_hash
        signed = manifest["artifacts"].get("signed_science_claim_bundle.json", {}).get("sha256")
        if signed:
            chain_root["signed_bundle_hash"] = signed
            manifest.setdefault("canonical_signed_bundle", {})["sha256"] = signed
        path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def sync_formal_artifacts(pf_release: pathlib.Path, root: pathlib.Path) -> None:
    src_dir = root / "tests" / "pcs" / "fixtures" / "formal" / "labtrust"
    for name in FORMAL_ARTIFACTS:
        src = src_dir / name
        if src.is_file():
            (pf_release / name).write_bytes(src.read_bytes())


def main() -> int:
    root = pathlib.Path(__file__).resolve().parents[1]
    pcs_core = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else root.parent / "pcs-core"
    canonical = pcs_core / "examples" / "labtrust-release"
    pf_release = root / "tests" / "pcs" / "fixtures" / "labtrust-release"
    if not canonical.is_dir():
        print(f"error: canonical RC dir not found: {canonical}", file=sys.stderr)
        return 1
    pf_release.mkdir(parents=True, exist_ok=True)
    for name in PF_ARTIFACTS:
        src = canonical / name
        if not src.is_file():
            print(f"error: missing canonical artifact {src}", file=sys.stderr)
            return 1
        dst = pf_release / name
        dst.write_bytes(src.read_bytes())
    manifest_src = canonical / "RELEASE_FIXTURE_MANIFEST.json"
    rc: dict = {}
    pf_commit = "0f659b90c80c46a6bbfd51b0d37ea723b032fb9d"
    if manifest_src.is_file():
        rc = json.loads(manifest_src.read_text(encoding="utf-8"))
        pf_commit = rc.get("provability_fabric_commit", pf_commit)
    pf_manifest_path = pf_release / "FIXTURE_MANIFEST.json"
    pf_manifest = {
        "profile": "labtrust-release-v0.1",
        "bundle_id": "scb-pcs-qc-release-v0.1",
        "claim_id": "claim-pcs-qc-release-v0.1",
        "certified_source": "pcs-core/examples/labtrust-release/science_claim_bundle.certified.json",
        "canonical_rc": "pcs-core/examples/labtrust-release",
        "pf_source_commit": pf_commit,
        "labtrust_gym_commit": rc.get("labtrust_gym_commit"),
        "certifyedge_commit": rc.get("certifyedge_commit"),
        "scientific_memory_commit": rc.get("scientific_memory_commit"),
        "pf_outputs": ["verification_result.json", "signed_science_claim_bundle.json"],
        "negative_fixtures": [
            "invalid_singular_runtime_receipt_bundle.json",
            "invalid_trace_certificate_singular_bundle.json",
            "invalid_mismatched_trace_hash.json",
            "invalid_missing_signature_or_digest.json",
            "invalid_zero_source_commit_release.json",
            "invalid_rejected_certificate.json",
            "invalid_stale_artifact.json",
        ],
        "regenerate": "make sync-pcs-rc-fixtures",
        "artifact_hashes": {
            name: sha256_file(pf_release / name)
            for name in (*PF_ARTIFACTS, *FORMAL_ARTIFACTS)
            if (pf_release / name).is_file()
        },
    }
    pf_manifest = {k: v for k, v in pf_manifest.items() if v is not None}
    pf_manifest_path.write_text(json.dumps(pf_manifest, indent=2) + "\n", encoding="utf-8")
    # Legacy pf_handoff.json: local-dev / negative tests only (forbidden with --release-mode).
    certified = json.loads((pf_release / "science_claim_bundle.certified.json").read_text(encoding="utf-8"))
    handoff = {
        "schema_version": "v0",
        "certified_bundle": "science_claim_bundle.certified.json",
        "certified_bundle_hash": sha256_file(pf_release / "science_claim_bundle.certified.json"),
        "certificate_id": certified["certificates"][0]["certificate_id"],
        "trace_hash": certified["runtime_receipts"][0]["trace_hash"],
    }
    (pf_release / "pf_handoff.json").write_text(json.dumps(handoff, indent=2) + "\n", encoding="utf-8")
    for src_name, dst_name in PF_PROTOCOL_FROM_RC:
        src = canonical / src_name
        if src.is_file():
            (pf_release / dst_name).write_bytes(src.read_bytes())
    refresh_handoff_to_pf(pf_release)
    for src_name, dst_name in PF_PROTOCOL_ALSO_COPY:
        src = canonical / src_name
        if src.is_file():
            (pf_release / dst_name).write_bytes(src.read_bytes())
    sm_report = canonical / "scientific_memory_import_report.json"
    if sm_report.is_file():
        (pf_release / "scientific_memory_import_report.json").write_bytes(sm_report.read_bytes())
    sync_formal_artifacts(pf_release, root)
    prune_pf_release_manifest(pf_release)
    examples = pcs_core / "examples"
    for src_name, dst_name in PF_PROTOCOL_FALLBACK:
        dst = pf_release / dst_name
        if dst.is_file():
            continue
        src = examples / src_name
        if src.is_file():
            dst.write_bytes(src.read_bytes())
    invalid_script = root / "scripts" / "pcs-freeze-labtrust-release-invalid.py"
    if invalid_script.is_file():
        import subprocess

        subprocess.run([sys.executable, str(invalid_script), str(pf_release)], check=True)
    print(f"OK: synced PF fixtures from {canonical}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
