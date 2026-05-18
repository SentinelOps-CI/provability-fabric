#!/usr/bin/env python3
"""Normalize labtrust-release fixtures to LF and align handoff file-digest pins."""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys

RELEASE = pathlib.Path(__file__).resolve().parents[1] / "tests" / "pcs" / "fixtures" / "labtrust-release"
CERTIFIED = "science_claim_bundle.certified.json"
CERTIFIED_HASH = "sha256:30b5b731a298922c41432de82c4ea407ec732f1e54f85b45ed9344ee5ec2c536"


def file_digest(path: pathlib.Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return "sha256:" + hashlib.sha256(data).hexdigest()


def write_lf(path: pathlib.Path, data: dict) -> None:
    text = json.dumps(data, indent=2, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8", newline="\n")


def normalize_bytes(path: pathlib.Path) -> None:
    raw = path.read_bytes()
    lf = raw.replace(b"\r\n", b"\n")
    if not lf.endswith(b"\n"):
        lf += b"\n"
    path.write_bytes(lf)


def main() -> int:
    if not RELEASE.is_dir():
        print(f"missing {RELEASE}", file=sys.stderr)
        return 1

    cert_path = RELEASE / CERTIFIED
    if not cert_path.is_file():
        print(f"missing {cert_path}", file=sys.stderr)
        return 1
    normalize_bytes(cert_path)
    digest = file_digest(cert_path)
    if digest != CERTIFIED_HASH:
        print(f"warning: {CERTIFIED} digest {digest} != expected {CERTIFIED_HASH}", file=sys.stderr)

    for name in ("handoff_to_pf.json",):
        path = RELEASE / name
        doc = json.loads(path.read_text(encoding="utf-8"))
        doc["invariants"]["certified_bundle_hash"] = digest
        if "input_artifacts" in doc and CERTIFIED in doc["input_artifacts"]:
            doc["input_artifacts"][CERTIFIED]["sha256"] = digest
        write_lf(path, doc)

    legacy = RELEASE / "pf_handoff.json"
    if legacy.is_file():
        leg = json.loads(legacy.read_text(encoding="utf-8"))
        leg["certified_bundle_hash"] = digest
        write_lf(legacy, leg)

    manifest_path = RELEASE / "release_manifest.json"
    if manifest_path.is_file():
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        if "chain_root" in manifest:
            manifest["chain_root"]["certified_bundle_hash"] = digest
        arts = manifest.get("artifacts") or {}
        if CERTIFIED in arts:
            arts[CERTIFIED]["sha256"] = digest
        write_lf(manifest_path, manifest)

    fixture_manifest = RELEASE / "FIXTURE_MANIFEST.json"
    if fixture_manifest.is_file():
        fm = json.loads(fixture_manifest.read_text(encoding="utf-8"))
        fm.setdefault("artifact_hashes", {})[CERTIFIED] = digest
        write_lf(fixture_manifest, fm)

    print(f"OK: LF-aligned labtrust-release; certified file digest {digest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
