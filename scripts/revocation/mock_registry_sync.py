#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Sync revocation list from a mock registry fixture and validate merge logic.

CI dry-run path: fetch remote list over local HTTP, merge with in-tree list,
verify signatures/fields, write synced artifact. Does not open PRs or hit live
external registries.
"""

from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from typing import Any

REPO = Path(__file__).resolve().parents[2]
DEFAULT_LOCAL = REPO / "runtime" / "admission-controller" / "revocation" / "revocations.json"
DEFAULT_REMOTE = REPO / "tests" / "fixtures" / "registry" / "remote_revocations.json"
DEFAULT_OUT = REPO / "runtime" / "admission-controller" / "revocation" / "revocations.synced.json"
REQUIRED_KEYS = ("sig", "reason", "ts", "revoked_by")


def validate_list(data: dict[str, Any], label: str) -> None:
    assert "version" in data, f"{label}: missing version"
    assert isinstance(data.get("revocations"), list), f"{label}: revocations not a list"
    for i, entry in enumerate(data["revocations"]):
        for key in REQUIRED_KEYS:
            assert key in entry, f"{label}: entry {i} missing {key}"
        assert str(entry["sig"]).startswith("sha256:"), f"{label}: entry {i} bad sig prefix"


def merge_lists(local: dict[str, Any], remote: dict[str, Any]) -> dict[str, Any]:
    by_sig: dict[str, dict[str, Any]] = {}
    for entry in local["revocations"] + remote["revocations"]:
        by_sig[entry["sig"]] = entry
    merged = {
        "version": remote.get("version") or local.get("version") or "1.0",
        "created_at": remote.get("created_at") or local.get("created_at"),
        "source": "mock-registry-sync",
        "revocations": sorted(by_sig.values(), key=lambda e: e["sig"]),
    }
    validate_list(merged, "merged")
    return merged


def package_and_sign(payload: dict[str, Any], key: bytes) -> dict[str, Any]:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    digest = hashlib.sha256(raw).hexdigest()
    mac = hmac.new(key, raw, hashlib.sha256).hexdigest()
    return {
        "algorithm": "HMAC-SHA256",
        "sha256": digest,
        "signature": mac,
        "bytes": len(raw),
    }


def verify_package(payload: dict[str, Any], package: dict[str, Any], key: bytes) -> None:
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    digest = hashlib.sha256(raw).hexdigest()
    mac = hmac.new(key, raw, hashlib.sha256).hexdigest()
    assert package["sha256"] == digest, "package sha256 mismatch"
    assert hmac.compare_digest(package["signature"], mac), "package signature mismatch"


class _Handler(BaseHTTPRequestHandler):
    remote_path: Path

    def log_message(self, format: str, *args: Any) -> None:  # noqa: A003
        return

    def do_GET(self) -> None:  # noqa: N802
        if self.path not in ("/v1/revocations", "/v1/revocations.json"):
            self.send_response(404)
            self.end_headers()
            return
        body = self.remote_path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def serve_fixture(path: Path, port: int) -> HTTPServer:
    _Handler.remote_path = path
    server = HTTPServer(("127.0.0.1", port), _Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    return server


def fetch_remote(url: str) -> dict[str, Any]:
    import urllib.request

    with urllib.request.urlopen(url, timeout=10) as resp:  # noqa: S310 — local CI only
        return json.loads(resp.read().decode("utf-8"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local", type=Path, default=DEFAULT_LOCAL)
    parser.add_argument("--remote-fixture", type=Path, default=DEFAULT_REMOTE)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--port", type=int, default=8765)
    parser.add_argument(
        "--signing-key",
        default=os.environ.get("REVOCATION_SYNC_SIGNING_KEY", "ci-local-revocation-key"),
    )
    args = parser.parse_args()

    local = json.loads(args.local.read_text(encoding="utf-8"))
    validate_list(local, "local")

    server = serve_fixture(args.remote_fixture, args.port)
    try:
        remote = fetch_remote(f"http://127.0.0.1:{args.port}/v1/revocations")
        validate_list(remote, "remote")
        merged = merge_lists(local, remote)
        key = args.signing_key.encode("utf-8")
        package = package_and_sign(merged, key)
        verify_package(merged, package, key)

        args.out.parent.mkdir(parents=True, exist_ok=True)
        envelope = {"list": merged, "package": package}
        args.out.write_text(json.dumps(envelope, indent=2) + "\n", encoding="utf-8")

        # Prove sync added remote-only entries
        local_sigs = {e["sig"] for e in local["revocations"]}
        remote_sigs = {e["sig"] for e in remote["revocations"]}
        merged_sigs = {e["sig"] for e in merged["revocations"]}
        assert remote_sigs - local_sigs, "fixture must introduce at least one new revocation"
        assert remote_sigs.issubset(merged_sigs)
        assert local_sigs.issubset(merged_sigs)
        print(
            f"ok: synced {len(merged['revocations'])} entries "
            f"(+{len(remote_sigs - local_sigs)} remote); "
            f"package sha256={package['sha256'][:16]}..."
        )
        print(f"wrote {args.out}")
        return 0
    finally:
        server.shutdown()


if __name__ == "__main__":
    raise SystemExit(main())
