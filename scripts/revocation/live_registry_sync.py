#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Fetch + merge + sign revocation list against a live external registry.

Fail-closed: requires REVOCATION_REGISTRY_URL (and optional bearer token).
Dry-run/mock path remains scripts/revocation/mock_registry_sync.py.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

# Reuse merge/sign helpers from the mock sync module (same package dir).
sys.path.insert(0, str(Path(__file__).resolve().parent))
from mock_registry_sync import (  # noqa: E402
    DEFAULT_LOCAL,
    DEFAULT_OUT,
    merge_lists,
    package_and_sign,
    validate_list,
    verify_package,
)

REPO = Path(__file__).resolve().parents[2]


def fetch_remote(url: str, token: str | None, timeout: int = 30) -> dict[str, Any]:
    headers = {"Accept": "application/json", "User-Agent": "provability-fabric-revocation-sync/1.0"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:  # noqa: S310 — ops-gated URL
            if resp.status != 200:
                raise RuntimeError(f"registry HTTP {resp.status}")
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        raise RuntimeError(f"registry HTTP {exc.code}: {exc.reason}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"registry unreachable: {exc.reason}") from exc


def merge_lists_live(local: dict[str, Any], remote: dict[str, Any]) -> dict[str, Any]:
    merged = merge_lists(local, remote)
    merged["source"] = "live-registry-sync"
    return merged


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local", type=Path, default=DEFAULT_LOCAL)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--registry-url",
        default=os.environ.get("REVOCATION_REGISTRY_URL", ""),
        help="External registry URL (or REVOCATION_REGISTRY_URL)",
    )
    parser.add_argument(
        "--token",
        default=os.environ.get("REVOCATION_REGISTRY_TOKEN", ""),
        help="Optional bearer token (or REVOCATION_REGISTRY_TOKEN)",
    )
    parser.add_argument(
        "--signing-key",
        default=os.environ.get("REVOCATION_SYNC_SIGNING_KEY", ""),
        help="HMAC key (or REVOCATION_SYNC_SIGNING_KEY); required for live",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=Path(
            os.environ.get(
                "REVOCATION_LIVE_REPORT",
                "runtime/admission-controller/revocation/live-sync-report.json",
            )
        ),
    )
    args = parser.parse_args()

    missing: list[str] = []
    if not str(args.registry_url).strip():
        missing.append("REVOCATION_REGISTRY_URL")
    if not str(args.signing_key).strip():
        missing.append("REVOCATION_SYNC_SIGNING_KEY")
    if missing:
        print(
            f"error: live revocation sync invoked without config: {', '.join(missing)}",
            file=sys.stderr,
        )
        print("fail-closed: configure secrets and re-dispatch mode=live", file=sys.stderr)
        return 1

    local = json.loads(args.local.read_text(encoding="utf-8"))
    validate_list(local, "local")

    remote = fetch_remote(str(args.registry_url).strip(), str(args.token).strip() or None)
    validate_list(remote, "remote")
    merged = merge_lists_live(local, remote)
    key = str(args.signing_key).encode("utf-8")
    package = package_and_sign(merged, key)
    verify_package(merged, package, key)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    envelope = {"list": merged, "package": package, "live_registry": True}
    args.out.write_text(json.dumps(envelope, indent=2) + "\n", encoding="utf-8")

    local_sigs = {e["sig"] for e in local["revocations"]}
    remote_sigs = {e["sig"] for e in remote["revocations"]}
    report = {
        "live_registry": True,
        "registry_url": str(args.registry_url).strip(),
        "local_count": len(local_sigs),
        "remote_count": len(remote_sigs),
        "merged_count": len(merged["revocations"]),
        "added_from_remote": len(remote_sigs - local_sigs),
        "package_sha256": package["sha256"],
        "source": merged["source"],
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    print(f"wrote {args.out}")
    print(f"wrote {args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
