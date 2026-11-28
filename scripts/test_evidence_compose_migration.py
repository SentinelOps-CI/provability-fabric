#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify local Compose migration against actual HTTP and PostgreSQL."""
import argparse
import json
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, urlopen


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tokens", type=Path, required=True)
    parser.add_argument("--phase", choices=["seed", "verify"], required=True)
    args = parser.parse_args()
    tokens = json.loads(args.tokens.read_text(encoding="utf-8"))
    base = "http://127.0.0.1:8004/api/v1"

    def call(path, method="GET", payload=None, token=None, expected=200):
        headers = {"Content-Type": "application/json"}
        if token is not None:
            headers["Authorization"] = "Bearer " + tokens[token]
        request = Request(base + path, method=method, headers=headers,
                          data=None if payload is None else json.dumps(payload).encode())
        try:
            with urlopen(request, timeout=5) as response:
                code, body = response.status, response.read()
        except HTTPError as exc:
            code, body = exc.code, exc.read()
        assert code == expected, (path, code, expected)
        return json.loads(body)

    health = call("/health")
    assert health["storage_backend"] == "postgres" and health["database"] == "connected"
    cert = {"bundle_id": "compose-fixture", "policy_hash": "policy",
            "proof_hash": "proof", "automata_hash": "automata",
            "labeler_hash": "labeler", "ni_claim": "fixture",
            "ni_monitor": "inapplicable", "sidecar_build": "fixture",
            "tenant_id": "tenant-a", "session_id": "compose-session",
            "timestamp": "2026-01-01T00:00:00Z"}
    call("/evidence/cert", "POST", cert, expected=401)
    call("/evidence/cert", "POST", cert, "b", 403)
    if args.phase == "seed":
        call("/evidence/cert", "POST", cert, "a", 201)
        call("/evidence/cert", "POST", {**cert, "tenant_id": "tenant-b"}, "b", 201)
    call("/evidence/search", "POST", {"tenant_id": "tenant-b"}, "a", 403)
    for token, tenant in (("a", "tenant-a"), ("b", "tenant-b")):
        result = call("/evidence/search", "POST", {}, token)
        assert result["total"] == 1 and len(result["certificates"]) == 1
        assert result["certificates"][0]["tenant_id"] == tenant
        assert result["certificates"][0]["session_id"] == "compose-session"
    print(f"PASS {args.phase}: authenticated tenant-isolated PostgreSQL evidence")


if __name__ == "__main__":
    main()
