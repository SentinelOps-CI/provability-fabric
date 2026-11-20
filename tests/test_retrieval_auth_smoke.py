"""Offline controls for the disposable retrieval authorization HTTP probe.

These tests verify signing interoperability and fail-closed harness behavior.
The integration workflow separately runs the probe against the real Rust API.
"""
from __future__ import annotations

import base64
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from retrieval_auth_smoke import (
    AUDIENCE, ISSUER, KID, claims_for, run_probes, sign_token, verifier_key_map,
)


@unittest.skipUnless(shutil.which("openssl"), "OpenSSL is required for Ed25519 tests")
class SignedRetrievalSmokeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="pf-jwt-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.private = self.root / "private.pem"
        subprocess.run(
            ["openssl", "genpkey", "-algorithm", "Ed25519",
             "-out", str(self.private)],
            check=True, capture_output=True, timeout=15,
        )

    def test_verifier_key_map_is_public_key_only(self) -> None:
        keys = verifier_key_map(self.private)
        self.assertEqual(set(keys), {KID})
        raw = base64.urlsafe_b64decode(keys[KID] + "==")
        self.assertEqual(len(raw), 32)
        public = subprocess.run(
            ["openssl", "pkey", "-in", str(self.private), "-pubout", "-outform", "DER"],
            check=True, capture_output=True, timeout=15,
        ).stdout
        self.assertEqual(raw, public[-32:])
        self.assertNotIn("PRIVATE", json.dumps(keys))

    def test_compact_signature_verifies_with_independent_openssl(self) -> None:
        token = sign_token(self.private, claims_for("tenant-a", "alice", int(time.time())))
        pieces = token.split(".")
        self.assertEqual(len(pieces), 3)
        header = json.loads(base64.urlsafe_b64decode(pieces[0] + "=="))
        self.assertEqual(header, {"alg": "EdDSA", "kid": KID, "typ": "JWT"})
        claims = json.loads(base64.urlsafe_b64decode(pieces[1] + "=="))
        self.assertEqual(claims["iss"], ISSUER)
        self.assertEqual(claims["aud"], AUDIENCE)
        self.assertEqual(claims["allowed_labels"], ["public"])
        signing_input = self.root / "signed-message"
        signing_input.write_text(".".join(pieces[:2]), encoding="ascii")
        signature = self.root / "signature"
        signature.write_bytes(base64.urlsafe_b64decode(pieces[2] + "=="))
        self.assertEqual(signature.stat().st_size, 64)
        public_pem = self.root / "public.pem"
        with public_pem.open("wb") as stream:
            subprocess.run(
                ["openssl", "pkey", "-in", str(self.private), "-pubout"],
                stdout=stream, check=True, stderr=subprocess.PIPE, timeout=15,
            )
        cmd = [
            "openssl", "pkeyutl", "-verify", "-pubin", "-inkey", str(public_pem),
            "-rawin", "-in", str(signing_input), "-sigfile", str(signature),
        ]
        self.assertEqual(
            subprocess.run(cmd, capture_output=True, timeout=15).returncode, 0,
        )
        signing_input.write_text("tampered." + pieces[1], encoding="ascii")
        self.assertNotEqual(
            subprocess.run(cmd, capture_output=True, timeout=15).returncode, 0,
        )

    def test_rejects_remote_or_non_http_probe_targets(self) -> None:
        for target in ["https://127.0.0.1:8080", "http://example.net", "file:///etc/passwd"]:
            with self.subTest(target=target):
                with self.assertRaises(ValueError):
                    run_probes(target, self.private)

    def test_positive_probe_must_return_real_success(self) -> None:
        with patch("retrieval_auth_smoke.request_gateway", return_value=(403, {})):
            with self.assertRaisesRegex(RuntimeError, "valid signed public request"):
                run_probes("http://127.0.0.1:8080", self.private)

    def test_signed_acceptance_needs_complete_attributed_receipt(self) -> None:
        with patch(
            "retrieval_auth_smoke.request_gateway",
            return_value=(200, {"total_count": 0, "results": []}),
        ):
            with self.assertRaisesRegex(RuntimeError, "unexpected receipt"):
                run_probes("http://127.0.0.1:8080", self.private)

    def test_every_negative_probe_must_really_deny(self) -> None:
        def fabricated_allow(_url: str, payload: dict) -> tuple[int, dict]:
            return 200, {
                "results": [], "total_count": 0,
                "receipt": {
                    "tenant": payload["tenant"], "subject_id": payload["subject_id"],
                    "sign_alg": "ed25519", "sig": "fixture-signature",
                },
            }

        with patch("retrieval_auth_smoke.request_gateway", side_effect=fabricated_allow):
            with self.assertRaisesRegex(RuntimeError, "legacy unsigned token"):
                run_probes("http://127.0.0.1:8080", self.private)


if __name__ == "__main__":
    unittest.main()
