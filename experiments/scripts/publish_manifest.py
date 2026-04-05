#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# SHA-256 manifest for publish/ (tamper-evident bundle). Excludes MANIFEST.sha256 itself.

from __future__ import annotations

import hashlib
import os
import subprocess
import sys
from pathlib import Path


def write_publish_manifest_sha256(publish_dir: Path) -> None:
    """Write MANIFEST.sha256: one line per file ``<sha256>  <relative/path>`` (sorted by path)."""
    publish_dir = Path(publish_dir).resolve()
    if not publish_dir.is_dir():
        raise FileNotFoundError("publish dir not found: %s" % publish_dir)
    rows: list[tuple[str, str]] = []
    for path in sorted(publish_dir.rglob("*")):
        if not path.is_file():
            continue
        rel = path.relative_to(publish_dir).as_posix()
        if rel == "MANIFEST.sha256":
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        rows.append((digest, rel))
    rows.sort(key=lambda t: t[1])
    body = "".join("%s  %s\n" % (d, r) for d, r in rows)
    (publish_dir / "MANIFEST.sha256").write_text(body, encoding="utf-8")


def maybe_gpg_detach_sign_manifest(publish_dir: Path) -> None:
    """
    If PF_GPG_SIGN_MANIFEST is 1/true, run gpg --detach-sign on MANIFEST.sha256.
    Optional key: PF_GPG_KEY_ID (passed to gpg -u). Writes MANIFEST.sha256.asc.
    """
    flag = os.environ.get("PF_GPG_SIGN_MANIFEST", "").strip().lower()
    if flag not in ("1", "true", "yes", "on"):
        return
    publish_dir = Path(publish_dir).resolve()
    manifest = publish_dir / "MANIFEST.sha256"
    asc = publish_dir / "MANIFEST.sha256.asc"
    if not manifest.is_file():
        return
    cmd = ["gpg", "--batch", "--yes", "--detach-sign", "--armor", "-o", str(asc), str(manifest)]
    kid = os.environ.get("PF_GPG_KEY_ID", "").strip()
    if kid:
        cmd[1:1] = ["--local-user", kid]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    except FileNotFoundError:
        print("PF_GPG_SIGN_MANIFEST set but gpg not found", file=sys.stderr)
        return
    except subprocess.TimeoutExpired:
        print("gpg --detach-sign timed out", file=sys.stderr)
        return
    if r.returncode != 0:
        print("gpg sign failed: %s" % (r.stderr or r.stdout or "unknown"), file=sys.stderr)
    else:
        print("Wrote %s" % asc)


def verify_publish_manifest_sha256(publish_dir: Path) -> list[str]:
    """Return list of error strings; empty means every listed file matches."""
    publish_dir = Path(publish_dir).resolve()
    manifest_path = publish_dir / "MANIFEST.sha256"
    if not manifest_path.exists():
        return ["MANIFEST.sha256 missing in publish dir"]
    errors: list[str] = []
    for line in manifest_path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        parts = line.split(None, 1)
        if len(parts) != 2:
            errors.append("bad manifest line: %r" % line[:80])
            continue
        expected_hex, rel = parts[0], parts[1].strip()
        fpath = publish_dir / rel
        if not fpath.is_file():
            errors.append("manifest lists missing file: %s" % rel)
            continue
        got = hashlib.sha256(fpath.read_bytes()).hexdigest()
        if got != expected_hex:
            errors.append("hash mismatch for %s (expected %s..., got %s...)" % (rel, expected_hex[:12], got[:12]))
    return errors


def main() -> int:
    ap = __import__("argparse").ArgumentParser(description="Write or verify publish/MANIFEST.sha256")
    ap.add_argument("publish_dir", type=Path, help="Path to publish/")
    ap.add_argument("--verify", action="store_true", help="Verify instead of write")
    args = ap.parse_args()
    if args.verify:
        errs = verify_publish_manifest_sha256(args.publish_dir)
        if errs:
            for e in errs:
                print(e, file=sys.stderr)
            return 1
        print("MANIFEST.sha256: all entries match.")
        return 0
    write_publish_manifest_sha256(args.publish_dir)
    pd = args.publish_dir.resolve()
    print("Wrote %s/MANIFEST.sha256" % pd)
    maybe_gpg_detach_sign_manifest(args.publish_dir)
    return 0


if __name__ == "__main__":
    sys.exit(main())
