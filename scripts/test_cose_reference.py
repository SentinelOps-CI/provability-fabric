#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Independently regenerate the fixed COSE_Sign1 vector using OpenSSL."""
import json
from pathlib import Path
import subprocess
import tempfile


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


def main():
    protected = cbor({1: -19})
    payload = cbor({"content_hash": bytes([1]) * 32, "timestamp": 1000,
                    "issuer": "test_issuer", "subject": "test_subject",
                    "request_id": "test_request"})
    sig_structure = cbor(["Signature1", protected, b"", payload])
    with tempfile.TemporaryDirectory(prefix="pf-cose-fixture-") as tmp:
        root = Path(tmp)
        key = root / "key.der"
        # Fixed RFC 8410 PKCS#8 Ed25519 seed fixture, never a deployed key.
        key.write_bytes(bytes.fromhex("302e020100300506032b657004220420") + bytes([41]) * 32)
        pub = root / "public.der"
        public = openssl("pkey", "-inform", "DER", "-in", key, "-pubout", "-outform", "DER")
        prefix = bytes.fromhex("302a300506032b6570032100")
        if not public.startswith(prefix) or len(public) != len(prefix) + 32:
            raise RuntimeError("unexpected Ed25519 public key format")
        pub.write_bytes(public)
        message = root / "message"
        message.write_bytes(sig_structure)
        signature = openssl("pkeyutl", "-sign", "-rawin", "-keyform", "DER",
                            "-inkey", key, "-in", message)
        sig = root / "signature"
        sig.write_bytes(signature)
        openssl("pkeyutl", "-verify", "-rawin", "-pubin", "-keyform", "DER",
                "-inkey", pub, "-in", message, "-sigfile", sig)
        message.write_bytes(sig_structure + b"\x00")
        bad = subprocess.run(["openssl", "pkeyutl", "-verify", "-rawin", "-pubin",
                              "-keyform", "DER", "-inkey", str(pub), "-in", str(message),
                              "-sigfile", str(sig)], timeout=15,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if bad.returncode != 1:
            raise RuntimeError("altered reference message was not rejected")
    envelope = head(6, 18) + cbor([protected, {}, payload, signature])
    observed = {name: value.hex() for name, value in {
        "protected": protected, "payload": payload, "sig_structure": sig_structure,
        "signature": signature, "public": public[len(prefix):], "envelope": envelope}.items()}
    fixture = Path(__file__).resolve().parents[1] / "runtime/sidecar-watcher/tests/fixtures/cose-sign1-ed25519.json"
    expected = json.loads(fixture.read_text())
    if observed != expected:
        raise RuntimeError("independent COSE fixture mismatch")
    print("PASS: six byte-exact COSE/Ed25519 reference fields; altered message rejected")


if __name__ == "__main__":
    main()
