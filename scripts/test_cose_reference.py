#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Independently regenerate the fixed COSE_Sign1 vector using OpenSSL."""
import json
from pathlib import Path
import subprocess
import tempfile


from verify_cose_sign1 import head, cbor, openssl


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
    # Independent external consumer invocation. The fixture public key and
    # expected payload are passed separately from the envelope under test.
    with tempfile.TemporaryDirectory(prefix="pf-cose-consumer-") as tmp:
        root = Path(tmp)
        verifier = Path(__file__).with_name("verify_cose_sign1.py")
        key, wrong, expected_json, wire = (root / n for n in
            ("public.pem", "wrong.pem", "expected.json", "envelope.cbor"))
        import base64
        import sys
        der = bytes.fromhex("302a300506032b6570032100") + bytes.fromhex(expected["public"])
        key.write_bytes(b"-----BEGIN PUBLIC KEY-----\n" + base64.b64encode(der) + b"\n-----END PUBLIC KEY-----\n")
        wrong_private = root / "wrong-private.pem"
        openssl("genpkey", "-algorithm", "Ed25519", "-out", wrong_private)
        openssl("pkey", "-in", wrong_private, "-pubout", "-out", wrong)
        fields = {"content_hash": "01" * 32, "timestamp": 1000, "issuer": "test_issuer",
                  "subject": "test_subject", "request_id": "test_request"}
        def check(name, candidate, payload_fields, trusted, ok):
            wire.write_bytes(candidate)
            expected_json.write_text(json.dumps(payload_fields), encoding="utf-8")
            result = subprocess.run([sys.executable, str(verifier), "--envelope", str(wire),
                "--expected-payload", str(expected_json), "--trusted-public-key", str(trusted)],
                capture_output=True, text=True, timeout=20)
            if (result.returncode == 0) != ok:
                raise RuntimeError(f"{name}: unexpected verification outcome: {result.stderr}")
            print(f"PASS external consumer {name}")
        check("valid tagged profile", envelope, fields, key, True)
        check("wrong key", envelope, fields, wrong, False)
        check("altered signature", envelope[:-1] + bytes([envelope[-1] ^ 1]), fields, key, False)
        check("untagged legacy envelope", envelope[1:], fields, key, False)
        check("trailing data", envelope + bytes([0]), fields, key, False)
        check("changed expected request", envelope, {**fields, "request_id": "different"}, key, False)
        check("changed expected hash", envelope, {**fields, "content_hash": "02" * 32}, key, False)
        check("old algorithm header", envelope[:4] + bytes([0x27]) + envelope[5:], fields, key, False)
        check("private key as trust input", envelope, fields, wrong_private, False)


if __name__ == "__main__":
    main()
