#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Generate deterministic crypto fixtures for tests/fixtures/crypto/.
# Usage: python scripts/generate_crypto_fixtures.py

from __future__ import annotations

import base64
import json
import os
from pathlib import Path

# Fixed seed for reproducibility (32 bytes)
FIXED_SEED = bytes(range(32))


def main() -> None:
    try:
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
    except ImportError:
        print("Install cryptography: pip install cryptography")
        raise SystemExit(1)

    repo_root = Path(__file__).resolve().parent.parent
    out_dir = repo_root / "tests" / "fixtures" / "crypto"
    out_dir.mkdir(parents=True, exist_ok=True)

    # Deterministic key from fixed seed (Ed25519 allows 32-byte seed)
    private_key = Ed25519PrivateKey.from_private_bytes(FIXED_SEED)
    public_key = private_key.public_key()

    private_pem = private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    )
    public_pem = public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo,
    )

    (out_dir / "ed25519_private.pem").write_bytes(private_pem)
    (out_dir / "ed25519_public.pem").write_bytes(public_pem)

    # Sample payload (canonical JSON) and sign it for DSSE envelope
    payload_obj = {
        "receipt_id": "fixture-receipt-1",
        "tenant": "test",
        "subject_id": "subject-1",
        "query_hash": "a" * 64,
        "index_shard": "0",
        "timestamp": 1000000,
        "result_hash": "b" * 64,
        "result_count": 1,
        "query_time_ms": 10,
        "signature": "",
    }
    payload_json = json.dumps(payload_obj, sort_keys=True, separators=(",", ":"))
    payload_b64 = base64.b64encode(payload_json.encode()).decode()
    payload_bytes = payload_json.encode()

    signature_bytes = private_key.sign(payload_bytes)
    sig_b64 = base64.b64encode(signature_bytes).decode()

    envelope = {
        "payloadType": "application/vnd.provability-fabric.access-receipt",
        "payload": payload_b64,
        "signatures": [
            {
                "keyid": "receipt_signer_v1",
                "sig": sig_b64,
                "alg": "ed25519",
            }
        ],
    }
    (out_dir / "dsse_sample_envelope.json").write_text(
        json.dumps(envelope, indent=2), encoding="utf-8"
    )
    print("Generated", out_dir)


if __name__ == "__main__":
    main()
