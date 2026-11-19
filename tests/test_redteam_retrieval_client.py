"""Offline client/HTTP regression checks for the retrieval gateway ABAC probe."""

from __future__ import annotations

import asyncio
import hashlib
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / "redteam"))
from abac_fuzz import ABACFuzzTester, TestCase


def reference_documents():
    return {
        "alpha-public": {"tenant": "alpha", "labels": frozenset(["public"]),
                         "content_sha256": hashlib.sha256(b"alpha fixture").hexdigest()},
        "beta-public": {"tenant": "beta", "labels": frozenset(["public"]),
                        "content_sha256": hashlib.sha256(b"beta fixture").hexdigest()},
    }


def example_reply(payload, doc_id="alpha-public", content="alpha fixture"):
    return {
        "results": [{"document_id": doc_id, "content": content,
                     "content_hash": hashlib.sha256(content.encode()).hexdigest(),
                     "labels": ["public"], "metadata": {}, "score": 0.8}],
        "total_count": 1,
        "receipt": {"tenant": payload["tenant"], "subject_id": payload["subject_id"],
                    "index_shard": f"shard_{payload['tenant']}", "result_count": 1,
                    "sign_alg": "ed25519", "sig": "unverified-test-sig"},
    }


class FakeResponse:
    def __init__(self, status, data):
        self.status = status
        self.data = data

    async def __aenter__(self):
        return self

    async def __aexit__(self, *_):
        return False

    async def json(self):
        if isinstance(self.data, Exception):
            raise self.data
        return self.data

    async def text(self):
        return "fixture service response"


class FakeSession:
    def __init__(self, status=200, reply=example_reply):
        self.status = status
        self.reply = reply
        self.url = None
        self.payload = None

    def post(self, url, *, json, headers):
        self.url = url
        self.payload = json
        return FakeResponse(self.status, self.reply(json))


class RetrievalClientTests(unittest.TestCase):
    def setUp(self):
        self.harness = ABACFuzzTester(
            "http://127.0.0.1:8080/", capability_token="fixture-only-token",
            reference_documents=reference_documents(), seed=7,
        )
        self.case = TestCase(
            tenant="alpha", subject_id="fixture-subject", subject_roles=["user"],
            query="reference corpus", expected_labels=["public"],
            expected_tenant="alpha", test_id="positive-alpha",
        )

    def test_actual_route_and_request_shape(self):
        session = FakeSession()
        result = asyncio.run(self.harness.execute_test_case(session, self.case))
        self.assertEqual(session.url, "http://127.0.0.1:8080/query")
        self.assertEqual(session.payload["tenant"], "alpha")
        self.assertEqual(session.payload["capability_token"], "fixture-only-token")
        self.assertEqual(session.payload["labels_filter"], ["public"])
        self.assertEqual(session.payload["limit"], 10)
        self.assertNotIn("subject_roles", session.payload)
        self.assertNotIn("test_id", session.payload)
        self.assertTrue(result.success)
        self.assertEqual(result.result_count, 1)
        self.assertFalse(result.cross_tenant_leak)

    def test_malformed_response_is_not_success(self):
        for reply in (lambda _: {}, lambda _: ValueError("malformed JSON")):
            with self.subTest(reply=reply):
                session = FakeSession(reply=reply)
                result = asyncio.run(self.harness.execute_test_case(session, self.case))
                self.assertFalse(result.success)
                self.assertNotEqual(result.error_message, None)

    def test_unknown_and_cross_tenant_documents_are_violations(self):
        for doc_id, content, cross, unauthorized in (
            ("beta-public", "beta fixture", True, False),
            ("unregistered", "unregistered fixture", False, True),
        ):
            with self.subTest(doc_id=doc_id):
                session = FakeSession(reply=lambda p, d=doc_id, c=content: example_reply(p, d, c))
                result = asyncio.run(self.harness.execute_test_case(session, self.case))
                self.assertTrue(result.success)
                self.assertEqual(result.cross_tenant_leak, cross)
                self.assertEqual(result.unauthorized_access, unauthorized)

    def test_expected_empty_token_denial_is_observed(self):
        case = TestCase(**{**vars(self.case), "denial_reason": "empty_token"})
        session = FakeSession(status=403)
        result = asyncio.run(self.harness.execute_test_case(session, case))
        self.assertTrue(result.success)
        self.assertTrue(result.denial_observed)
        self.assertEqual(session.payload["capability_token"], "")

    def test_secret_label_denial_is_observed(self):
        case = TestCase(**{**vars(self.case), "expected_labels": ["secret"],
                           "denial_reason": "secret_label"})
        session = FakeSession(status=403)
        result = asyncio.run(self.harness.execute_test_case(session, case))
        self.assertTrue(result.denial_observed)
        self.assertEqual(session.payload["labels_filter"], ["secret"])
        self.assertEqual(session.payload["capability_token"], "fixture-only-token")

    def test_unexpected_allow_for_denial_fails(self):
        case = TestCase(**{**vars(self.case), "denial_reason": "empty_token"})
        session = FakeSession(status=200)
        result = asyncio.run(self.harness.execute_test_case(session, case))
        self.assertFalse(result.success)
        self.assertFalse(result.denial_observed)

    def test_unexpected_http_error_fails(self):
        session = FakeSession(status=404)
        result = asyncio.run(self.harness.execute_test_case(session, self.case))
        self.assertFalse(result.success)
        self.assertIn("HTTP 404", result.error_message)

    def test_each_tenant_has_three_explicit_controls(self):
        self.harness.generate_test_cases(12)
        self.assertEqual(len(self.harness.test_cases), 12)
        for tenant in ("alpha", "beta"):
            controls = [x for x in self.harness.test_cases if x.tenant == tenant and x.test_id.startswith(tenant + "-")]
            self.assertEqual(len(controls), 3)
            self.assertEqual({x.denial_reason for x in controls}, {None, "empty_token", "secret_label"})
        with self.assertRaises(ValueError):
            self.harness.generate_test_cases(5)

    def test_reproducible_cases(self):
        self.harness.generate_test_cases(24)
        other = ABACFuzzTester(
            "http://127.0.0.1:8080/", capability_token="fixture-only-token",
            reference_documents=reference_documents(), seed=7,
        )
        other.generate_test_cases(24)
        self.assertEqual(self.harness.test_cases, other.test_cases)

    def test_empty_result_cannot_establish_tenant_isolation(self):
        self.harness.generate_test_cases(6)
        for case in self.harness.test_cases:
            if case.denial_reason:
                self.harness.results.append(
                    asyncio.run(self.harness.execute_test_case(FakeSession(status=403), case))
                )
            else:
                def empty_reply(payload):
                    response = example_reply(payload)
                    response["results"] = []
                    response["total_count"] = 0
                    response["receipt"]["result_count"] = 0
                    return response
                self.harness.results.append(
                    asyncio.run(self.harness.execute_test_case(FakeSession(reply=empty_reply), case))
                )
        report = self.harness.generate_report()
        self.assertEqual(report["execution"]["status"], "FAIL")
        self.assertEqual(report["execution"]["document_observations"], 0)


if __name__ == "__main__":
    unittest.main()
