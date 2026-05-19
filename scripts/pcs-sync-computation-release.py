#!/usr/bin/env python3
"""Sync PF computation-release fixtures from pcs-core/examples/computation-release/."""
from __future__ import annotations

import hashlib
import json
import pathlib
import shutil
import sys

PF_ARTIFACTS = (
    "science_claim_bundle.certified.json",
    "verification_result.json",
    "signed_science_claim_bundle.json",
)

PF_PROTOCOL = (
    ("handoff_to_pf.json", "handoff_to_pf.json"),
    ("handoff_manifest.bundle_to_verifier.v0.json", "handoff_to_pf.json"),
    ("release_manifest.v0.json", "release_manifest.v0.json"),
    ("release_chain_validation_result.v0.json", "release_chain_validation_result.json"),
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
    canonical = pcs_core / "examples" / "computation-release"
    pf_release = root / "tests" / "pcs" / "fixtures" / "computation-release"
    if not canonical.is_dir():
        print(f"error: canonical computation-release dir not found: {canonical}", file=sys.stderr)
        return 1
    if pf_release.exists():
        shutil.rmtree(pf_release)
    shutil.copytree(canonical, pf_release)
    registry_src = pcs_core / "examples" / "artifact_registry.valid.json"
    if registry_src.is_file():
        (pf_release / "artifact_registry.json").write_bytes(registry_src.read_bytes())
    manifest_src = canonical / "RELEASE_FIXTURE_MANIFEST.json"
    pf_commit = "c333333333333333333333333333333333333333"
    if manifest_src.is_file():
        rc = json.loads(manifest_src.read_text(encoding="utf-8"))
        pf_commit = rc.get("provability_fabric_commit", pf_commit)
    pf_manifest = {
        "profile": "computation-release-v0",
        "workflow_id": "scientific_computation.reproducibility_v0",
        "admission_profile": "scientific_computation_reproducibility",
        "canonical_rc": "pcs-core/examples/computation-release",
        "pf_source_commit": pf_commit,
        "regenerate": "python3 scripts/pcs-sync-computation-release.py pcs-core",
    }
    (pf_release / "FIXTURE_MANIFEST.json").write_text(
        json.dumps(pf_manifest, indent=2) + "\n",
        encoding="utf-8",
    )
    for src_name, dst_name in PF_PROTOCOL:
        src = canonical / src_name
        if src.is_file():
            (pf_release / dst_name).write_bytes(src.read_bytes())
    print(f"OK: synced computation-release fixtures from {canonical}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
