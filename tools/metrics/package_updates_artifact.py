#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Package and HMAC-sign a publish-updates markdown artifact for CI dry-run.

Validates packaging (tar + manifest) and signature round-trip against a local
mock registry directory. Live registry publish remains secret/dispatch-gated.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
import tarfile
from pathlib import Path


def build_package(src: Path, out_dir: Path, key: bytes) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)
    raw = src.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    sig = hmac.new(key, raw, hashlib.sha256).hexdigest()

    blob = out_dir / "updates.md"
    blob.write_bytes(raw)
    manifest = {
        "name": "updates.md",
        "sha256": digest,
        "bytes": len(raw),
        "algorithm": "HMAC-SHA256",
        "signature": sig,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")

    tarball = out_dir / "updates-package.tar.gz"
    with tarfile.open(tarball, "w:gz") as tar:
        tar.add(blob, arcname="updates.md")
        tar.add(out_dir / "manifest.json", arcname="manifest.json")

    # Mock registry "publish": copy tarball into registry root and verify
    registry = out_dir / "mock-registry"
    registry.mkdir(exist_ok=True)
    published = registry / "updates-package.tar.gz"
    published.write_bytes(tarball.read_bytes())

    # Verify round-trip
    with tarfile.open(published, "r:gz") as tar:
        members = {m.name for m in tar.getmembers()}
        assert "updates.md" in members and "manifest.json" in members
        extracted_md = tar.extractfile("updates.md")
        extracted_man = tar.extractfile("manifest.json")
        assert extracted_md is not None and extracted_man is not None
        md_bytes = extracted_md.read()
        man = json.loads(extracted_man.read().decode("utf-8"))
    assert hashlib.sha256(md_bytes).hexdigest() == man["sha256"]
    expect = hmac.new(key, md_bytes, hashlib.sha256).hexdigest()
    assert hmac.compare_digest(man["signature"], expect), "signature verify failed"
    assert b"Recent Updates" in md_bytes

    return {
        "package": str(tarball),
        "registry_object": str(published),
        "sha256": digest,
        "signature_prefix": sig[:16],
        "live_registry": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--src",
        type=Path,
        default=Path(os.environ.get("PUBLISH_UPDATES_OUT", "docs/updates.dry-run.md")),
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path(os.environ.get("PUBLISH_UPDATES_PACKAGE_DIR", "artifacts/updates-package")),
    )
    parser.add_argument(
        "--signing-key",
        default=os.environ.get("PUBLISH_UPDATES_SIGNING_KEY", "ci-local-publish-key"),
    )
    args = parser.parse_args()
    if not args.src.is_file():
        raise SystemExit(f"missing source artifact: {args.src}")
    report = build_package(args.src, args.out_dir, args.signing_key.encode("utf-8"))
    report_path = args.out_dir / "package-report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"package_updates_artifact: PASS -> {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
