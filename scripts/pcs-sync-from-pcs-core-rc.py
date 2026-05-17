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


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


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
        "artifact_hashes": {name: sha256_file(pf_release / name) for name in PF_ARTIFACTS},
    }
    pf_manifest = {k: v for k, v in pf_manifest.items() if v is not None}
    pf_manifest_path.write_text(json.dumps(pf_manifest, indent=2) + "\n", encoding="utf-8")
    certified = json.loads((pf_release / "science_claim_bundle.certified.json").read_text(encoding="utf-8"))
    handoff = {
        "schema_version": "v0",
        "certified_bundle": "science_claim_bundle.certified.json",
        "certified_bundle_hash": sha256_file(pf_release / "science_claim_bundle.certified.json"),
        "certificate_id": certified["certificates"][0]["certificate_id"],
        "trace_hash": certified["runtime_receipts"][0]["trace_hash"],
    }
    (pf_release / "pf_handoff.json").write_text(json.dumps(handoff, indent=2) + "\n", encoding="utf-8")
    invalid_script = root / "scripts" / "pcs-freeze-labtrust-release-invalid.py"
    if invalid_script.is_file():
        import subprocess

        subprocess.run([sys.executable, str(invalid_script), str(pf_release)], check=True)
    print(f"OK: synced PF fixtures from {canonical}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
