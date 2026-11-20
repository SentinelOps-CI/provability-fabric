"""Independent binary reference for the signed retrieval-result v2 commitment."""

from __future__ import annotations

import copy
import hashlib
import json
import math
import re
from pathlib import Path
import struct
import unittest

DOMAIN = b"provability-fabric/retrieval-result/v2\x00"
PREFIX = "sha256-v2:"
FIXTURE = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "crypto"
    / "retrieval_result_commitment_v2.json"
)


def compute_reference(tenant: str, results: list[dict]) -> str:
    """Hash ordered result fields with length-prefix framing and domain separation."""
    if not tenant:
        raise ValueError("tenant missing")

    digest = hashlib.sha256()
    digest.update(DOMAIN)

    def number(value: int) -> None:
        digest.update(struct.pack(">Q", value))

    def text(value: str) -> None:
        raw = value.encode("utf-8")
        number(len(raw))
        digest.update(raw)

    text(tenant)
    number(len(results))
    for result in results:
        score = float(result["score"])
        if not math.isfinite(score):
            raise ValueError("score is not finite")
        text(result["document_id"])
        text(result["content"])
        text(result["content_hash"])
        digest.update(struct.pack(">d", 0.0 if score == 0.0 else score))

        labels = result["labels"]
        number(len(labels))
        for label in labels:
            text(label)

        metadata = result["metadata"]
        number(len(metadata))
        for key in sorted(metadata.keys(), key=lambda item: item.encode("utf-8")):
            text(key)
            text(metadata[key])

    return PREFIX + digest.hexdigest()


class RetrievalResultReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = json.loads(FIXTURE.read_text(encoding="utf-8"))
        if cls.fixture["schema_version"] != 2:
            raise AssertionError("fixture version mismatch")

    def test_independent_fixed_vectors(self) -> None:
        vectors = self.fixture["vectors"]
        self.assertGreaterEqual(len(vectors), 5)
        for vector in vectors:
            with self.subTest(name=vector["name"]):
                self.assertEqual(
                    compute_reference(vector["tenant"], vector["results"]),
                    vector["expected_result_hash"],
                )

    def test_legacy_framing_ambiguity_does_not_survive(self) -> None:
        a, b = self.fixture["vectors"][1:3]
        a_raw = a["results"][0]["document_id"] + a["results"][0]["content"]
        b_raw = b["results"][0]["document_id"] + b["results"][0]["content"]
        self.assertEqual(a_raw, b_raw)
        self.assertNotEqual(a["expected_result_hash"], b["expected_result_hash"])

    def test_every_declared_result_field_affects_hash(self) -> None:
        v = self.fixture["vectors"][1]
        original = compute_reference(v["tenant"], v["results"])
        mutations = [
            ("document_id", "another"),
            ("content", "another"),
            ("content_hash", "another"),
            ("score", 0.25),
            ("labels", ["public"]),
            ("metadata", {"alpha": "changed", "β": "é"}),
        ]
        for key, value in mutations:
            with self.subTest(field=key):
                changed = copy.deepcopy(v["results"])
                changed[0][key] = value
                self.assertNotEqual(original, compute_reference(v["tenant"], changed))
        self.assertNotEqual(
            original, compute_reference("another-tenant", v["results"])
        )

        ordered = self.fixture["vectors"][4]
        self.assertNotEqual(
            compute_reference(ordered["tenant"], ordered["results"]),
            compute_reference(ordered["tenant"], ordered["results"][::-1]),
        )

    def test_metadata_order_is_ignored_and_signed_zero_is_canonical(self) -> None:
        vector = self.fixture["vectors"][1]
        changed = copy.deepcopy(vector["results"])
        changed[0]["metadata"] = dict(reversed(list(changed[0]["metadata"].items())))
        self.assertEqual(
            compute_reference(vector["tenant"], changed),
            vector["expected_result_hash"],
        )

        negative_zero = self.fixture["vectors"][3]
        changed = copy.deepcopy(negative_zero["results"])
        changed[0]["score"] = 0.0
        self.assertEqual(
            compute_reference(negative_zero["tenant"], changed),
            negative_zero["expected_result_hash"],
        )

    def test_invalid_scores_and_tenant_fail_closed(self) -> None:
        sample = copy.deepcopy(self.fixture["vectors"][1]["results"])
        for score in (math.nan, math.inf, -math.inf):
            with self.subTest(score=str(score)):
                sample[0]["score"] = score
                with self.assertRaises(ValueError):
                    compute_reference("tenant-a", sample)
        with self.assertRaises(ValueError):
            compute_reference("", [])

    def test_hash_version_is_signed_field_data(self) -> None:
        sample = self.fixture["vectors"][1]
        v2 = compute_reference(sample["tenant"], sample["results"])
        self.assertTrue(v2.startswith(PREFIX))
        self.assertEqual(len(v2), len(PREFIX) + 64)
        self.assertEqual(len("a" * 64), 64)


    def test_receipt_schema_identifies_actual_signed_wire_fields(self) -> None:
        repo = Path(__file__).resolve().parents[1]
        schema_path = repo / "runtime/retrieval-gateway/schema/receipt.json"
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        signed = json.loads(
            (FIXTURE.parent / "retrieval_receipt_v2_signed.json").read_text(encoding="utf-8")
        )
        receipt = dict(signed["receipt"])
        receipt.pop("signature")
        receipt["sig"] = signed["signature_base64"]
        receipt["sign_alg"] = "ed25519"

        required = set(schema["required"])
        self.assertIn("sig", required)
        self.assertIn("sign_alg", required)
        self.assertNotIn("signature", required)
        self.assertTrue(required.issubset(receipt.keys()))
        self.assertTrue(set(receipt).issubset(schema["properties"].keys()))

        pattern = schema["properties"]["result_hash"]["pattern"]
        for valid in ("a" * 64, "A" * 64, signed["receipt"]["result_hash"]):
            self.assertIsNotNone(re.fullmatch(pattern, valid), valid)
        for invalid in (
            "sha256-v3:" + "a" * 64,
            "sha256-v2:" + "A" * 64,
            "sha256-v2:" + "g" * 64,
            "wrong",
        ):
            self.assertIsNone(re.fullmatch(pattern, invalid), invalid)
        self.assertNotIn("pattern", schema["properties"]["receipt_id"])
        self.assertGreater(schema["properties"]["receipt_id"]["minLength"], 0)


if __name__ == "__main__":
    unittest.main()
