#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Verify the restricted PF COSE_Sign1 profile against external expectations.

This is a byte-exact verifier for the documented fixed application encoding,
not a generic CBOR parser, trust discovery system or execution verifier.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

MAX_BYTES = 1024 * 1024
SPKI_PREFIX = bytes.fromhex("302a300506032b6570032100")


def head(major, length):
    if length < 24:
        return bytes([major * 32 + length])
    for width, tag in ((1, 24), (2, 25), (4, 26), (8, 27)):
        if length < 1 << (8 * width):
            return bytes([major * 32 + tag]) + length.to_bytes(width, "big")
    raise ValueError("CBOR integer out of range")


def cbor(value):
    if isinstance(value, int):
        return head(0, value) if value >= 0 else head(1, -1 - value)
    if isinstance(value, bytes):
        return head(2, len(value)) + value
    if isinstance(value, str):
        raw = value.encode("utf-8")
        return head(3, len(raw)) + raw
    if isinstance(value, list):
        return head(4, len(value)) + b"".join(map(cbor, value))
    if isinstance(value, dict):
        return head(5, len(value)) + b"".join(
            cbor(key) + cbor(item) for key, item in value.items())
    raise TypeError(type(value))


def openssl(*args):
    return subprocess.run(["openssl", *map(str, args)], check=True,
                          timeout=15, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE).stdout



def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate JSON field")
        result[key] = value
    return result


def bounded_read(path):
    with path.open("rb") as stream:
        raw = stream.read(MAX_BYTES + 1)
    if len(raw) > MAX_BYTES:
        raise ValueError("profile input exceeds byte limit")
    return raw


def expected_payload(raw):
    fields = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_pairs)
    if not isinstance(fields, dict) or set(fields) != {
        "content_hash", "timestamp", "issuer", "subject", "request_id"
    }:
        raise ValueError("unexpected payload fields")
    content_hash = fields["content_hash"]
    if (not isinstance(content_hash, str) or len(content_hash) != 64
            or any(c not in "0123456789abcdef" for c in content_hash)):
        raise ValueError("content_hash must contain 64 lowercase hexadecimal characters")
    stamp = fields["timestamp"]
    if type(stamp) is not int or not 0 <= stamp < 2**64:
        raise ValueError("timestamp must be an unsigned 64-bit integer")
    for key in ("issuer", "subject", "request_id"):
        if not isinstance(fields[key], str):
            raise ValueError("identity fields must be strings")
    # Exact profile field order, independent of expectation JSON order.
    return cbor({"content_hash": bytes.fromhex(content_hash), "timestamp": stamp,
                 "issuer": fields["issuer"], "subject": fields["subject"],
                 "request_id": fields["request_id"]})


def verify_envelope(envelope, expected, trusted_key):
    protected = cbor({1: -19})
    payload = expected_payload(expected)
    prefix = head(6, 18) + head(4, 4) + cbor(protected) + cbor({}) + cbor(payload) + head(2, 64)
    if len(envelope) != len(prefix) + 64 or not envelope.startswith(prefix):
        raise ValueError("envelope differs from the exact tagged Sign1 profile or expected payload")
    # Independently selected key; reject RSA, other curves, and private-key input.
    # Snapshot the public key before checking type and invoking verification.
    with tempfile.TemporaryDirectory(prefix="pf-cose-verify-") as tmp:
        root = Path(tmp)
        key = root / "trusted.pem"
        key.write_bytes(bounded_read(trusted_key))
        der = openssl("pkey", "-pubin", "-in", key, "-outform", "DER")
        if len(der) != len(SPKI_PREFIX) + 32 or not der.startswith(SPKI_PREFIX):
            raise ValueError("trusted public key is not Ed25519")
        public, message, signature = (root / n for n in ("public.der", "message", "signature"))
        public.write_bytes(der)
        message.write_bytes(cbor(["Signature1", protected, b"", payload]))
        signature.write_bytes(envelope[-64:])
        openssl("pkeyutl", "-verify", "-rawin", "-pubin", "-keyform", "DER",
                "-inkey", public, "-in", message, "-sigfile", signature)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--envelope", required=True, type=Path)
    parser.add_argument("--expected-payload", required=True, type=Path)
    parser.add_argument("--trusted-public-key", required=True, type=Path)
    args = parser.parse_args()
    try:
        verify_envelope(bounded_read(args.envelope), bounded_read(args.expected_payload),
                        args.trusted_public_key)
    except (OSError, ValueError, TypeError, OverflowError, subprocess.SubprocessError) as exc:
        parser.exit(1, f"COSE verification failed: {exc}\n")
    print("PASS: exact expected COSE payload and trusted-key signature verified; execution authenticity not established")


if __name__ == "__main__":
    main()
