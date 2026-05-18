#!/usr/bin/env python3
"""Refresh ReleaseManifest artifact sha256 pins from on-disk files (LF-neutral file digests)."""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys


def digest(path: pathlib.Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def refresh(path: pathlib.Path) -> None:
    base = path.parent
    manifest = json.loads(path.read_text(encoding="utf-8"))
    for name, entry in manifest.get("artifacts", {}).items():
        artifact = base / name
        if artifact.is_file():
            entry["sha256"] = digest(artifact)
    cert = manifest.get("artifacts", {}).get("science_claim_bundle.certified.json", {}).get("sha256")
    signed = manifest.get("artifacts", {}).get("signed_science_claim_bundle.json", {}).get("sha256")
    if cert:
        manifest.setdefault("chain_root", {})["certified_bundle_hash"] = cert
    if signed:
        manifest.setdefault("chain_root", {})["signed_bundle_hash"] = signed
        manifest.setdefault("canonical_signed_bundle", {})["sha256"] = signed
    rcr = manifest.get("release_chain_validation_result")
    if isinstance(rcr, dict) and "path" in rcr:
        p = base / str(rcr["path"])
        if p.is_file():
            rcr["sha256"] = digest(p)
    path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: refresh-release-manifest-pins.py <artifact-dir>", file=sys.stderr)
        return 2
    base = pathlib.Path(sys.argv[1])
    for name in ("release_manifest.v0.json", "release_manifest.json"):
        path = base / name
        if path.is_file():
            refresh(path)
            print(f"refreshed {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
