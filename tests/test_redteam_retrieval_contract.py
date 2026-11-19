"""Independent retrieval gateway reference-corpus and wire-contract controls."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "redteam"))
from retrieval_contract import inspect_query_response, load_reference_documents


def sample_manifest() -> dict:
    return {
        "schema_version": 1,
        "documents": [
            {"document_id": "alpha-pub", "tenant": "alpha", "labels": ["public"],
             "content_sha256": hashlib.sha256(b"alpha data").hexdigest()},
            {"document_id": "beta-pub", "tenant": "beta", "labels": ["public"],
             "content_sha256": hashlib.sha256(b"beta data").hexdigest()},
        ],
    }


def sample_response(doc_id="alpha-pub", content="alpha data", tenant="alpha") -> dict:
    return {
        "results": [{"document_id": doc_id, "content": content,
                     "content_hash": hashlib.sha256(content.encode()).hexdigest(),
                     "labels": ["public"], "metadata": {}, "score": 0.8}],
        "total_count": 1,
        "receipt": {"tenant": tenant, "subject_id": "fixture-subject", "index_shard": f"shard_{tenant}",
                    "result_count": 1, "sign_alg": "ed25519", "sig": "fixture-nonverified-signature"},
    }


class RetrievalContractTests(unittest.TestCase):
    def setUp(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "corpus.json"
            path.write_text(json.dumps(sample_manifest()), encoding="utf-8")
            self.corpus = load_reference_documents(path)

    def inspect(self, payload):
        return inspect_query_response(
            payload, expected_tenant="alpha", expected_subject="fixture-subject",
            requested_labels=["public"], known_documents=self.corpus,
        )

    def test_known_document_is_observed(self):
        self.assertEqual(self.inspect(sample_response()), (1, False, False))

    def test_cross_tenant_document_is_flagged(self):
        response = sample_response("beta-pub", "beta data", "alpha")
        self.assertEqual(self.inspect(response), (1, True, False))

    def test_unknown_document_is_flagged(self):
        response = sample_response("unregistered", "unregistered data")
        self.assertEqual(self.inspect(response), (1, False, True))

    def test_tampered_content_is_flagged(self):
        response = sample_response("alpha-pub", "changed content")
        self.assertEqual(self.inspect(response), (1, False, True))

    def test_wrong_or_missing_receipt_fails(self):
        for field, value in (("tenant", "beta"), ("subject_id", "other"),
                             ("index_shard", "shard_beta"), ("sig", ""),
                             ("result_count", 0), ("sign_alg", "none")):
            with self.subTest(field=field):
                response = sample_response()
                response["receipt"][field] = value
                with self.assertRaises(ValueError):
                    self.inspect(response)

    def test_missing_or_wrong_count_fails(self):
        for response in ([], {}, {"results": []},
                         dict(sample_response(), total_count=7)):
            with self.subTest(response=response):
                with self.assertRaises(ValueError):
                    self.inspect(response)

    def test_metadata_mismatch_or_label_mismatch_is_detected(self):
        response = sample_response()
        response["results"][0]["labels"] = ["secret"]
        self.assertEqual(self.inspect(response), (1, False, True))
        response = sample_response()
        response["results"][0]["content_hash"] = "0" * 64
        self.assertEqual(self.inspect(response), (1, False, True))

    def test_valid_empty_result_is_not_a_positive_control(self):
        response = sample_response()
        response["results"] = []
        response["total_count"] = 0
        response["receipt"]["result_count"] = 0
        self.assertEqual(self.inspect(response), (0, False, False))

    def test_single_tenant_manifest_is_rejected(self):
        manifest = sample_manifest()
        manifest["documents"] = manifest["documents"][:1]
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "manifest.json"
            p.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_reference_documents(p)

    def test_duplicate_document_id_is_rejected(self):
        manifest = sample_manifest()
        manifest["documents"][1]["document_id"] = "alpha-pub"
        with tempfile.TemporaryDirectory() as directory:
            p = Path(directory) / "manifest.json"
            p.write_text(json.dumps(manifest), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_reference_documents(p)


if __name__ == "__main__":
    unittest.main()
