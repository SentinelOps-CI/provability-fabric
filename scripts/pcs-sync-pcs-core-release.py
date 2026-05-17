#!/usr/bin/env python3
"""Copy PF release outputs to pcs-core and refresh RELEASE_FIXTURE_MANIFEST hashes."""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return "sha256:" + h.hexdigest()


def main() -> int:
    if len(sys.argv) != 4:
        print("usage: pcs-sync-pcs-core-release.py <pf_release_dir> <pcs_core_release_dir> <pf_commit>", file=sys.stderr)
        return 2
    pf_release = pathlib.Path(sys.argv[1])
    pcs_release = pathlib.Path(sys.argv[2])
    pf_commit = sys.argv[3]
    pcs_release.mkdir(parents=True, exist_ok=True)
    for name in (
        "science_claim_bundle.certified.json",
        "verification_result.json",
        "signed_science_claim_bundle.json",
    ):
        src = pf_release / name
        dst = pcs_release / name
        dst.write_bytes(src.read_bytes())
    manifest_path = pcs_release / "RELEASE_FIXTURE_MANIFEST.json"
    if manifest_path.exists():
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
    else:
        data = {"schema_version": "v0", "artifacts": {}}
    data["provability_fabric_commit"] = pf_commit
    arts = data.setdefault("artifacts", {})
    arts["science_claim_bundle.certified.json"] = sha256_file(
        pf_release / "science_claim_bundle.certified.json"
    )
    arts["verification_result.json"] = sha256_file(pf_release / "verification_result.json")
    arts["signed_science_claim_bundle.json"] = sha256_file(pf_release / "signed_science_claim_bundle.json")
    manifest_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"OK: synced PF outputs to {pcs_release}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
