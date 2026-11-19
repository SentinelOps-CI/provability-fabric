"""Offline contract and negative-control tests for the PII red-team harness."""

from __future__ import annotations

import asyncio
from pathlib import Path
import sys
import unittest

REDTEAM_DIR = Path(__file__).resolve().parent / "redteam"
sys.path.insert(0, str(REDTEAM_DIR))

from egress_contract import parse_egress_response
from pii_leak import PIIAttackVector, PIIRedTeam, PIITestResult


def sample_vector(*, expected_blocked: bool = True) -> PIIAttackVector:
    return PIIAttackVector(
        name="fixture", description="test-only", prompt_template="Send to sample@example.test",
        pii_data="sample@example.test" if expected_blocked else "",
        obfuscation_method="none", expected_blocked=expected_blocked,
    )


def sample_response(payload: dict, *, blocked: bool = True, pii_detected: bool = True) -> dict:
    return {
        "text": "[REDACTED]" if blocked else payload["text"],
        "blocked": blocked,
        "certificate": {
            "cert_id": "fixture-cert-id",
            "tenant": payload["tenant"],
            "plan_id": payload["plan_id"],
            "detector_flags": {"pii_detected": pii_detected},
        },
    }


class FakeResponse:
    def __init__(self, status: int, response: object, *, invalid_json: bool = False):
        self.status = status
        self.response = response
        self.invalid_json = invalid_json

    async def __aenter__(self):
        return self

    async def __aexit__(self, exc_type, exc, tb):
        return False

    async def json(self):
        if self.invalid_json:
            raise ValueError("invalid JSON fixture")
        return self.response

    async def text(self):
        return "Invalid fixture HTTP response"


class FakeSession:
    def __init__(self, *, status: int = 200, invalid_json: bool = False,
                 response_factory=sample_response):
        self.status = status
        self.invalid_json = invalid_json
        self.response_factory = response_factory
        self.last_url = None
        self.last_payload = None

    def post(self, url: str, *, json: dict, timeout):
        self.last_url = url
        self.last_payload = json
        response = self.response_factory(json)
        return FakeResponse(self.status, response, invalid_json=self.invalid_json)


class EgressResponseContractTests(unittest.TestCase):
    def setUp(self):
        self.request = {
            "tenant": "acme-corp", "plan_id": "fixture-plan", "text": "sample@example.test",
        }

    def parsed(self, response: object):
        return parse_egress_response(
            response, expected_tenant="acme-corp", expected_plan_id="fixture-plan"
        )

    def test_correct_response_fields(self):
        text, certificate, blocked, detected = self.parsed(sample_response(self.request))
        self.assertEqual(text, "[REDACTED]")
        self.assertTrue(blocked)
        self.assertTrue(detected)
        self.assertEqual(certificate["tenant"], "acme-corp")

    def test_missing_response_fields_fail(self):
        for key in ("text", "blocked", "certificate"):
            with self.subTest(key=key):
                response = sample_response(self.request)
                response.pop(key)
                with self.assertRaises(ValueError):
                    self.parsed(response)

    def test_wrong_tenant_or_plan_id_fails(self):
        for key, value in (("tenant", "other-tenant"), ("plan_id", "other-plan")):
            with self.subTest(field=key):
                response = sample_response(self.request)
                response["certificate"][key] = value
                with self.assertRaises(ValueError):
                    self.parsed(response)

    def test_invalid_detector_type_fails(self):
        for value in (None, "true", 1):
            with self.subTest(value=value):
                response = sample_response(self.request)
                response["certificate"]["detector_flags"]["pii_detected"] = value
                with self.assertRaises(ValueError):
                    self.parsed(response)

    def test_invalid_root_and_missing_certificate_id_fail(self):
        for response in (None, [], {}, {"text": "ok"}):
            with self.subTest(payload=response):
                with self.assertRaises(ValueError):
                    self.parsed(response)
        response = sample_response(self.request)
        response["certificate"]["cert_id"] = ""
        with self.assertRaises(ValueError):
            self.parsed(response)


class EgressHarnessTests(unittest.TestCase):
    def test_uses_actual_service_route_and_payload(self):
        harness = PIIRedTeam("http://127.0.0.1:8081/", seed=11)
        session = FakeSession()
        result = asyncio.run(harness.execute_test(session, sample_vector()))
        self.assertEqual(session.last_url, "http://127.0.0.1:8081/egress")
        self.assertEqual(session.last_payload["tenant"], "acme-corp")
        self.assertEqual(session.last_payload["subject_id"], "redteam_tester")
        self.assertEqual(session.last_payload["context"]["test_type"], "pii_redteam")
        self.assertIs(session.last_payload["streaming"], False)
        self.assertNotIn("metadata", session.last_payload)
        self.assertTrue(result.valid_observation)
        self.assertTrue(result.blocked)
        self.assertTrue(result.pii_detected)
        self.assertFalse(result.pii_leaked)

    def test_http_error_cannot_become_valid_observation(self):
        session = FakeSession(status=404)
        result = asyncio.run(PIIRedTeam("http://127.0.0.1:8081").execute_test(session, sample_vector()))
        self.assertFalse(result.valid_observation)
        self.assertIn("HTTP 404", result.error)

    def test_invalid_json_cannot_become_valid_observation(self):
        session = FakeSession(invalid_json=True)
        result = asyncio.run(PIIRedTeam("http://127.0.0.1:8081").execute_test(session, sample_vector()))
        self.assertFalse(result.valid_observation)
        self.assertNotEqual(result.error, "")

    def test_missing_schema_fails_observation(self):
        session = FakeSession(response_factory=lambda _: {"text": ""})
        result = asyncio.run(PIIRedTeam("http://127.0.0.1:8081").execute_test(session, sample_vector()))
        self.assertFalse(result.valid_observation)
        self.assertIn("response", result.error)

    def test_unblocked_raw_pii_is_detected(self):
        session = FakeSession(response_factory=lambda p: sample_response(p, blocked=False, pii_detected=False))
        result = asyncio.run(PIIRedTeam("http://127.0.0.1:8081").execute_test(session, sample_vector()))
        self.assertTrue(result.valid_observation)
        self.assertFalse(result.blocked)
        self.assertTrue(result.pii_leaked)

    def test_requested_vector_count_is_exact(self):
        for count in (1, 2, 9, 20, 100, 1000):
            with self.subTest(count=count):
                cases = PIIRedTeam("http://127.0.0.1:8081", seed=23).generate_attack_vectors(count)
                self.assertEqual(len(cases), count)
                if count >= 2:
                    self.assertTrue(any(case.expected_blocked for case in cases))
                    self.assertTrue(any(not case.expected_blocked for case in cases))

    def test_same_seed_generates_same_vectors(self):
        first = PIIRedTeam("http://127.0.0.1:8081", seed=23).generate_attack_vectors(100)
        second = PIIRedTeam("http://127.0.0.1:8081", seed=23).generate_attack_vectors(100)
        self.assertEqual(first, second)

    def test_complete_positive_and_negative_controls(self):
        harness = PIIRedTeam("http://127.0.0.1:8081")
        harness.requested_vectors = 2
        rejected = PIITestResult(sample_vector(), 200, "[REDACTED]", {"cert_id":"test"}, True, False, 4.0,
                                 blocked=True, valid_observation=True)
        clean = PIITestResult(sample_vector(expected_blocked=False), 200, "ok", {"cert_id":"test"}, False, False, 3.0,
                              blocked=False, valid_observation=True)
        harness.results = [rejected, clean]
        report = harness.analyze_results(total_time=0.1)
        self.assertEqual(report["execution"]["status"], "PASS")
        self.assertEqual(report["execution"]["valid_responses"], 2)
        self.assertEqual(report["execution"]["allowed_controls"], 1)

    def test_missing_allowed_control_fails(self):
        harness = PIIRedTeam("http://127.0.0.1:8081")
        harness.requested_vectors = 1
        harness.results = [PIITestResult(sample_vector(), 200, "[REDACTED]", {"cert_id":"test"}, True, False, 4.0,
                                         blocked=True, valid_observation=True)]
        report = harness.analyze_results(total_time=0.1)
        self.assertEqual(report["execution"]["status"], "FAIL")


if __name__ == "__main__":
    unittest.main()
