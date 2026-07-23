#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Package and HMAC-sign a publish-updates markdown artifact.

CI dry-run: validates packaging against a local mock registry directory.
Live: uploads the signed tarball to UPDATES_REGISTRY_URL and records
live_registry=true in package-report.json. Fail-closed without registry URL/key.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
import sys
import tarfile
import urllib.error
import urllib.request
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

    return {
        "package": str(tarball),
        "sha256": digest,
        "signature": sig,
        "signature_prefix": sig[:16],
        "bytes": len(raw),
    }


def publish_mock(tarball: Path, out_dir: Path, key: bytes) -> dict:
    registry = out_dir / "mock-registry"
    registry.mkdir(exist_ok=True)
    published = registry / "updates-package.tar.gz"
    published.write_bytes(tarball.read_bytes())

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
        "registry_object": str(published),
        "live_registry": False,
    }


def publish_live(
    tarball: Path,
    registry_url: str,
    token: str | None,
    key: bytes,
) -> dict:
    raw = tarball.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    sig = hmac.new(key, raw, hashlib.sha256).hexdigest()
    headers = {
        "Content-Type": "application/gzip",
        "User-Agent": "provability-fabric-publish-updates/1.0",
        "X-Content-SHA256": digest,
        "X-Content-Signature": sig,
        "X-Signature-Algorithm": "HMAC-SHA256",
    }
    if token:
        headers["Authorization"] = f"Bearer {token}"

    req = urllib.request.Request(
        registry_url,
        data=raw,
        headers=headers,
        method="PUT",
    )
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:  # noqa: S310 — ops-gated URL
            status = resp.status
            body = resp.read()[:512]
    except urllib.error.HTTPError as exc:
        raise SystemExit(f"live registry HTTP {exc.code}: {exc.reason}") from exc
    except urllib.error.URLError as exc:
        raise SystemExit(f"live registry unreachable: {exc.reason}") from exc

    if status not in (200, 201, 202, 204):
        raise SystemExit(f"live registry unexpected status {status}: {body!r}")

    return {
        "registry_url": registry_url,
        "http_status": status,
        "live_registry": True,
        "uploaded_sha256": digest,
        "uploaded_signature_prefix": sig[:16],
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
    parser.add_argument(
        "--live-registry",
        action="store_true",
        default=os.environ.get("PUBLISH_UPDATES_LIVE_REGISTRY") == "1",
        help="Upload to UPDATES_REGISTRY_URL (fail-closed if unset)",
    )
    parser.add_argument(
        "--registry-url",
        default=os.environ.get("UPDATES_REGISTRY_URL", ""),
    )
    parser.add_argument(
        "--registry-token",
        default=os.environ.get("UPDATES_REGISTRY_TOKEN", ""),
    )
    args = parser.parse_args()
    if not args.src.is_file():
        raise SystemExit(f"missing source artifact: {args.src}")

    key = args.signing_key.encode("utf-8")
    base = build_package(args.src, args.out_dir, key)
    tarball = Path(base["package"])

    if args.live_registry:
        if not str(args.registry_url).strip():
            print(
                "error: live registry publish requires UPDATES_REGISTRY_URL",
                file=sys.stderr,
            )
            print("fail-closed: configure secrets and re-dispatch dry_run=false", file=sys.stderr)
            return 1
        if not str(args.signing_key).strip() or args.signing_key == "ci-local-publish-key":
            print(
                "error: live registry publish requires PUBLISH_UPDATES_SIGNING_KEY "
                "(not the CI-local default)",
                file=sys.stderr,
            )
            return 1
        live = publish_live(
            tarball,
            str(args.registry_url).strip(),
            str(args.registry_token).strip() or None,
            key,
        )
        report = {**base, **live}
    else:
        mock = publish_mock(tarball, args.out_dir, key)
        report = {**base, **mock}

    # Do not leak full signature in artifacts beyond prefix for mock path.
    report.pop("signature", None)

    report_path = args.out_dir / "package-report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"package_updates_artifact: PASS -> {report_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
