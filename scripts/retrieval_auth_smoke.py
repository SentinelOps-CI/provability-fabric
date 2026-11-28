#!/usr/bin/env python3
"""Exercise disposable, signed retrieval credentials against a local gateway.

These controls establish HTTP authentication and authorization decisions.
They do not establish isolation of documents: the ordinary gateway index is
empty, and this harness explicitly expects no returned reference documents.
"""
from __future__ import annotations

import argparse
import base64
import copy
import json
import secrets
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlsplit
from urllib.request import Request, urlopen

SPKI_PREFIX = bytes.fromhex("302a300506032b6570032100")
KID = "ephemeral-smoke-key"
AUDIENCE = "pf-retrieval-gateway"
ISSUER = "pf-compose-smoke"


def _run_openssl(*args: str) -> bytes:
    """Execute OpenSSL without shell interpolation or printing private input."""
    try:
        return subprocess.run(
            ["openssl", *args], check=True, capture_output=True, timeout=15,
        ).stdout
    except (subprocess.CalledProcessError, OSError, subprocess.TimeoutExpired) as exc:
        raise RuntimeError("OpenSSL signing-key operation failed") from exc


def _b64url(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).decode("ascii").rstrip("=")


def verifier_key_map(private_pem: Path) -> dict[str, str]:
    """Extract the Ed25519 raw public key from its exact ASN.1 SPKI encoding."""
    der = _run_openssl(
        "pkey", "-in", str(private_pem), "-pubout", "-outform", "DER",
    )
    if len(der) != len(SPKI_PREFIX) + 32 or not der.startswith(SPKI_PREFIX):
        raise ValueError("Expected an Ed25519 SubjectPublicKeyInfo")
    return {KID: _b64url(der[len(SPKI_PREFIX):])}


def _sign(private_pem: Path, message: bytes) -> bytes:
    """OpenSSL's Ed25519 pkeyutl expects input from a regular file."""
    with tempfile.TemporaryDirectory(prefix="pf-jwt-input-") as tmp:
        path = Path(tmp) / "signing-input"
        path.write_bytes(message)
        signature = _run_openssl(
            "pkeyutl", "-sign", "-inkey", str(private_pem),
            "-rawin", "-in", str(path),
        )
    if len(signature) != 64:
        raise RuntimeError("Ed25519 signature must be exactly 64 bytes")
    return signature


def sign_token(
    private_pem: Path, claims: dict[str, object], *, kid: str = KID,
) -> str:
    """Sign an explicit compact JWT using the disposable test issuer."""
    header = {"alg": "EdDSA", "typ": "JWT", "kid": kid}
    protected = _b64url(json.dumps(header, sort_keys=True, separators=(",", ":")).encode())
    payload = _b64url(json.dumps(claims, sort_keys=True, separators=(",", ":")).encode())
    message = f"{protected}.{payload}"
    return f"{message}.{_b64url(_sign(private_pem, message.encode('ascii')))}"


def claims_for(tenant: str, subject: str, now: int) -> dict[str, object]:
    """Produce a short-lived, explicitly scoped token with no elevated grants."""
    return {
        "iss": ISSUER, "aud": AUDIENCE, "sub": subject, "tenant": tenant,
        "iat": now - 5, "nbf": now - 5, "exp": now + 120,
        "jti": secrets.token_hex(16),
        "allowed_labels": ["public"], "capabilities": [],
    }


def request_gateway(url: str, payload: dict[str, object]) -> tuple[int, object]:
    data = json.dumps(payload).encode("utf-8")
    request = Request(
        url, method="POST", data=data,
        headers={"Content-Type": "application/json"},
    )
    try:
        with urlopen(request, timeout=10) as reply:
            code = reply.status
            body = reply.read(2_000_000)
    except HTTPError as exc:
        code = exc.code
        body = exc.read(2_000_000)
    except (URLError, TimeoutError) as exc:
        raise RuntimeError("Retrieval gateway was not reachable") from exc
    try:
        decoded = json.loads(body) if body else {}
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise RuntimeError(f"Unexpected HTTP {code} response format") from exc
    return code, decoded


def run_probes(base_url: str, private_pem: Path) -> None:
    """Check the real HTTP decision boundary using independent signed inputs."""
    parsed = urlsplit(base_url)
    if parsed.scheme != "http" or parsed.hostname not in {"localhost", "127.0.0.1", "::1"}:
        raise ValueError("Disposable smoke probes are restricted to loopback HTTP services")
    url = base_url.rstrip("/") + "/query"
    now = int(time.time())
    original = claims_for("smoke-tenant-a", "user_smoke", now)
    token = sign_token(private_pem, original)
    payload: dict[str, object] = {
        "query": "synthetic capability smoke", "tenant": original["tenant"],
        "subject_id": original["sub"], "capability_token": token,
        "labels_filter": ["public"], "limit": 10,
    }

    cases: list[tuple[str, dict[str, object], int]] = [
        ("valid signed public request", payload, 200),
    ]
    second_claim = claims_for("smoke-tenant-b", "user_smoke", now)
    cases.append((
        "valid signed second tenant",
        {**payload, "tenant": second_claim["tenant"],
         "capability_token": sign_token(private_pem, second_claim)},
        200,
    ))
    cases.extend([
        ("legacy unsigned token", {**payload, "capability_token": "any-nonempty-token"}, 403),
        ("token subject mismatch", {**payload, "subject_id": "other-subject"}, 403),
        ("token tenant mismatch", {**payload, "tenant": "smoke-tenant-b"}, 403),
        ("empty requested scope", {**payload, "labels_filter": []}, 403),
        ("unknown requested label", {**payload, "labels_filter": ["unknown"]}, 403),
        ("oversized result limit", {**payload, "limit": 101}, 400),
    ])
    expired = {**original, "iat": now - 90, "nbf": now - 90, "exp": now - 1}
    cases.append((
        "expired signed token",
        {**payload, "capability_token": sign_token(private_pem, expired)}, 403,
    ))
    future = {**original, "nbf": now + 300, "exp": now + 360}
    cases.append((
        "premature signed token",
        {**payload, "capability_token": sign_token(private_pem, future)}, 403,
    ))
    scope = {**original, "allowed_labels": ["private"]}
    cases.append((
        "label outside signed scope",
        {**payload, "capability_token": sign_token(private_pem, scope)}, 403,
    ))
    secret = {**original, "allowed_labels": ["secret"]}
    cases.append((
        "signed forbidden secret scope",
        {**payload, "labels_filter": ["secret"],
         "capability_token": sign_token(private_pem, secret)}, 403,
    ))
    private = {**original, "allowed_labels": ["private"]}
    cases.append((
        "private access without explicit capability",
        {**payload, "labels_filter": ["private"],
         "capability_token": sign_token(private_pem, private)}, 403,
    ))
    parts = token.split(".")
    altered = json.loads(base64.urlsafe_b64decode(parts[1] + "=" * (-len(parts[1]) % 4)))
    altered["tenant"] = "forged-tenant"
    parts[1] = _b64url(json.dumps(altered, separators=(",", ":")).encode())
    cases.append((
        "tampered signed claims",
        {**payload, "capability_token": ".".join(parts)}, 403,
    ))
    with tempfile.TemporaryDirectory(prefix="pf-untrusted-issuer-") as tmp:
        forged_key = Path(tmp) / "untrusted.pem"
        _run_openssl("genpkey", "-algorithm", "Ed25519", "-out", str(forged_key))
        cases.append((
            "signature from an untrusted key",
            {**payload, "capability_token": sign_token(forged_key, original)}, 403,
        ))
        for label, request_payload, expected_code in cases:
            code, response = request_gateway(url, request_payload)
            if code != expected_code:
                raise RuntimeError(
                    f"{label}: HTTP {code} differs from expected {expected_code}"
                )
            if code == 200:
                if not isinstance(response, dict):
                    raise RuntimeError(f"{label}: missing JSON response")
                receipt = response.get("receipt")
                if (not isinstance(receipt, dict)
                    or receipt.get("tenant") != request_payload["tenant"]
                    or receipt.get("subject_id") != request_payload["subject_id"]
                    or receipt.get("sign_alg") != "ed25519"
                    or not isinstance(receipt.get("sig"), str)
                    or not receipt["sig"]
                    or response.get("total_count") != 0
                    or response.get("results") != []):
                    raise RuntimeError(f"{label}: unexpected receipt or nonempty index")
            print(f"PASS {label}: HTTP {code}")
    print(
        "PASS 15 disposable retrieval-authorization HTTP probes; "
        "empty-index responses do not establish document isolation"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["export-public", "probe"])
    parser.add_argument("private_key", type=Path)
    parser.add_argument("--base-url", default="http://127.0.0.1:8080")
    args = parser.parse_args()
    try:
        if args.operation == "export-public":
            print(json.dumps(verifier_key_map(args.private_key), sort_keys=True))
        else:
            run_probes(args.base_url, args.private_key)
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"retrieval auth smoke failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
