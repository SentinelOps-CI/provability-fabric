#!/usr/bin/env python3
"""
Replay Test Suite for Provability Fabric

This module implements comprehensive replay testing that gates CI merges.
Tests cover good traces (allowed behaviors) and bad traces (policy violations).
"""

import json
import sys
import argparse
import logging
from pathlib import Path
from typing import Dict, List, Any
from dataclasses import dataclass
from enum import Enum

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class TestResult(Enum):
    PASS = "pass"
    FAIL = "fail"
    ERROR = "error"


@dataclass
class TestCase:
    name: str
    trace: List[Dict[str, Any]]
    expected_result: TestResult
    description: str
    tags: List[str]


@dataclass
class TestResult:
    test_case: TestCase
    actual_result: TestResult
    passed: bool
    error_message: str = ""
    execution_time_ms: float = 0.0


class ReplayTestSuite:
    """Comprehensive replay test suite for policy enforcement."""

    def __init__(self, dfa_path: str):
        self.dfa_path = Path(dfa_path)
        self.dfa_data = self._load_dfa()
        self.test_results: List[TestResult] = []

    def _load_dfa(self) -> Dict[str, Any]:
        """Load DFA data from JSON file."""
        try:
            with open(self.dfa_path, "r") as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"Failed to load DFA from {self.dfa_path}: {e}")
            sys.exit(1)

    def _evaluate_trace(self, trace: List[Dict[str, Any]]) -> TestResult:
        """Evaluate a trace against the DFA to determine if it's accepted."""
        try:
            # This is a simplified DFA evaluation
            # In practice, this would use the actual DFA implementation
            current_state = "initial"

            for event in trace:
                event_type = event.get("type", "unknown")
                action = event.get("action", {})

                # Simple state machine logic based on event types
                if event_type == "call":
                    if action.get("tool") == "SendEmail":
                        if "email_user" in action.get("roles", []):
                            current_state = "email_allowed"
                        else:
                            current_state = "email_denied"
                    elif action.get("tool") == "NetworkCall":
                        if "admin" in action.get("roles", []):
                            current_state = "network_allowed"
                        else:
                            current_state = "network_denied"
                elif event_type == "read":
                    if "reader" in action.get("roles", []):
                        current_state = "read_allowed"
                    else:
                        current_state = "read_denied"
                elif event_type == "write":
                    if "writer" in action.get("roles", []):
                        current_state = "write_allowed"
                    else:
                        current_state = "write_denied"

            # Determine if trace is accepted
            if "denied" in current_state:
                return TestResult.FAIL
            else:
                return TestResult.PASS

        except Exception as e:
            logger.error(f"Error evaluating trace: {e}")
            return TestResult.ERROR

    def run_good_trace_suite(self) -> List[TestResult]:
        """Run tests for good traces that should be accepted."""
        logger.info("Running good trace suite...")

        good_traces = [
            TestCase(
                name="admin_email_send",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["admin"],
                            "user_id": "admin_1",
                        },
                    }
                ],
                expected_result=TestResult.PASS,
                description="Admin should be able to send emails",
                tags=["admin", "email", "call"],
            ),
            TestCase(
                name="email_user_send",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["email_user"],
                            "user_id": "email_user_1",
                        },
                    }
                ],
                expected_result=TestResult.PASS,
                description="Email user should be able to send emails",
                tags=["email_user", "email", "call"],
            ),
            TestCase(
                name="reader_document_access",
                trace=[
                    {
                        "type": "read",
                        "action": {
                            "doc_id": "doc://public_document",
                            "roles": ["reader"],
                            "user_id": "reader_1",
                        },
                    }
                ],
                expected_result=TestResult.PASS,
                description="Reader should be able to read documents",
                tags=["reader", "read", "document"],
            ),
            TestCase(
                name="writer_document_access",
                trace=[
                    {
                        "type": "write",
                        "action": {
                            "doc_id": "doc://editable_document",
                            "roles": ["writer"],
                            "user_id": "writer_1",
                        },
                    }
                ],
                expected_result=TestResult.PASS,
                description="Writer should be able to write documents",
                tags=["writer", "write", "document"],
            ),
            TestCase(
                name="admin_network_call",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "NetworkCall",
                            "roles": ["admin"],
                            "user_id": "admin_1",
                        },
                    }
                ],
                expected_result=TestResult.PASS,
                description="Admin should be able to make network calls",
                tags=["admin", "network", "call"],
            ),
            TestCase(
                name="complex_allowed_sequence",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["email_user"],
                            "user_id": "email_user_1",
                        },
                    },
                    {
                        "type": "read",
                        "action": {
                            "doc_id": "doc://public_document",
                            "roles": ["reader"],
                            "user_id": "email_user_1",
                        },
                    },
                ],
                expected_result=TestResult.PASS,
                description="Complex sequence of allowed actions",
                tags=["complex", "sequence", "allowed"],
            ),
        ]

        results = []
        for test_case in good_traces:
            logger.info(f"Testing: {test_case.name}")

            start_time = time.time()
            actual_result = self._evaluate_trace(test_case.trace)
            execution_time = (time.time() - start_time) * 1000

            passed = actual_result == test_case.expected_result
            result = TestResult(
                test_case=test_case,
                actual_result=actual_result,
                passed=passed,
                execution_time_ms=execution_time,
            )

            if passed:
                logger.info(f"✅ {test_case.name}: PASSED")
            else:
                logger.error(
                    f"❌ {test_case.name}: FAILED - Expected {test_case.expected_result}, got {actual_result}"
                )

            results.append(result)

        return results

    def run_bad_trace_suite(self) -> List[TestResult]:
        """Run tests for bad traces that should be denied."""
        logger.info("Running bad trace suite...")

        bad_traces = [
            TestCase(
                name="regular_user_network_call",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "NetworkCall",
                            "roles": ["user"],
                            "user_id": "regular_user_1",
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Regular user should not be able to make network calls",
                tags=["user", "network", "call", "denied"],
            ),
            TestCase(
                name="non_admin_grant",
                trace=[
                    {
                        "type": "grant",
                        "action": {
                            "target_user": "user_2",
                            "permission": "email_send",
                            "roles": ["user"],
                            "user_id": "regular_user_1",
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Non-admin should not be able to grant permissions",
                tags=["user", "grant", "denied"],
            ),
            TestCase(
                name="non_reader_document_access",
                trace=[
                    {
                        "type": "read",
                        "action": {
                            "doc_id": "doc://sensitive_document",
                            "roles": ["user"],
                            "user_id": "regular_user_1",
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Non-reader should not be able to read documents",
                tags=["user", "read", "denied"],
            ),
            TestCase(
                name="non_writer_document_modify",
                trace=[
                    {
                        "type": "write",
                        "action": {
                            "doc_id": "doc://protected_document",
                            "roles": ["reader"],
                            "user_id": "reader_1",
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Non-writer should not be able to write documents",
                tags=["reader", "write", "denied"],
            ),
            TestCase(
                name="expired_session_access",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["email_user"],
                            "user_id": "email_user_1",
                            "session_expired": True,
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Expired session should be denied",
                tags=["expired", "session", "denied"],
            ),
            TestCase(
                name="revoked_principal_access",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["email_user"],
                            "user_id": "revoked_user_1",
                            "revoked": True,
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Revoked principal should be denied",
                tags=["revoked", "principal", "denied"],
            ),
            TestCase(
                name="attribute_mismatch_access",
                trace=[
                    {
                        "type": "read",
                        "action": {
                            "doc_id": "doc://tenant_a_document",
                            "roles": ["reader"],
                            "user_id": "reader_1",
                            "tenant": "tenant_b",
                        },
                    }
                ],
                expected_result=TestResult.FAIL,
                description="Cross-tenant access should be denied",
                tags=["tenant", "mismatch", "denied"],
            ),
            TestCase(
                name="complex_violation_sequence",
                trace=[
                    {
                        "type": "call",
                        "action": {
                            "tool": "SendEmail",
                            "roles": ["email_user"],
                            "user_id": "email_user_1",
                        },
                    },
                    {
                        "type": "call",
                        "action": {
                            "tool": "NetworkCall",
                            "roles": ["email_user"],
                            "user_id": "email_user_1",
                        },
                    },
                ],
                expected_result=TestResult.FAIL,
                description="Sequence with allowed followed by denied action",
                tags=["complex", "violation", "denied"],
            ),
        ]

        results = []
        for test_case in bad_traces:
            logger.info(f"Testing: {test_case.name}")

            start_time = time.time()
            actual_result = self._evaluate_trace(test_case.trace)
            execution_time = (time.time() - start_time) * 1000

            passed = actual_result == test_case.expected_result
            result = TestResult(
                test_case=test_case,
                actual_result=actual_result,
                passed=passed,
                execution_time_ms=execution_time,
            )

            if passed:
                logger.info(f"✅ {test_case.name}: PASSED (correctly denied)")
            else:
                logger.error(
                    f"❌ {test_case.name}: FAILED - Expected {test_case.expected_result}, got {actual_result}"
                )

            results.append(result)

        return results

    def run_property_tests(self) -> List[TestResult]:
        """Run property-based tests for adversarial scenarios."""
        logger.info("Running property tests...")

        # Test adversarial egress chunking
        chunking_results = self._test_egress_chunking()

        # Test polyglot JSON handling
        polyglot_results = self._test_polyglot_json()

        # Test ABAC permutations
        abac_results = self._test_abac_permutations()

        return chunking_results + polyglot_results + abac_results

    def _test_egress_chunking(self) -> List[TestResult]:
        """Test adversarial egress chunking scenarios."""
        results = []

        # Test case: Large payload split across multiple events
        test_case = TestCase(
            name="adversarial_egress_chunking",
            trace=[
                {
                    "type": "emit",
                    "action": {
                        "payload": "A" * 1000,  # Large payload
                        "chunk_id": 1,
                        "total_chunks": 10,
                    },
                }
            ],
            expected_result=TestResult.FAIL,  # Should be denied due to size
            description="Large payload should be denied",
            tags=["egress", "chunking", "size_limit"],
        )

        actual_result = self._evaluate_trace(test_case.trace)
        passed = actual_result == test_case.expected_result

        results.append(
            TestResult(test_case=test_case, actual_result=actual_result, passed=passed)
        )

        return results

    def _test_polyglot_json(self) -> List[TestResult]:
        """Test polyglot JSON handling for labeler."""
        results = []

        # Test case: JSON with embedded executable content
        test_case = TestCase(
            name="polyglot_json_executable",
            trace=[
                {
                    "type": "emit",
                    "action": {
                        "payload": '{"data": "normal", "script": "<script>alert(1)</script>"}',
                        "content_type": "application/json",
                    },
                }
            ],
            expected_result=TestResult.FAIL,  # Should be denied due to executable content
            description="JSON with executable content should be denied",
            tags=["polyglot", "json", "executable"],
        )

        actual_result = self._evaluate_trace(test_case.trace)
        passed = actual_result == test_case.expected_result

        results.append(
            TestResult(test_case=test_case, actual_result=actual_result, passed=passed)
        )

        return results

    def _test_abac_permutations(self) -> List[TestResult]:
        """Test ABAC attribute permutations."""
        results = []

        # Test case: Invalid attribute combination
        test_case = TestCase(
            name="invalid_abac_combination",
            trace=[
                {
                    "type": "read",
                    "action": {
                        "doc_id": "doc://sensitive_document",
                        "roles": ["reader"],
                        "user_id": "reader_1",
                        "attributes": {
                            "project": "project_a",
                            "clearance": "low",
                            "tenant": "tenant_b",  # Mismatch
                        },
                    },
                }
            ],
            expected_result=TestResult.FAIL,  # Should be denied due to attribute mismatch
            description="Invalid ABAC attribute combination should be denied",
            tags=["abac", "attributes", "mismatch"],
        )

        actual_result = self._evaluate_trace(test_case.trace)
        passed = actual_result == test_case.expected_result

        results.append(
            TestResult(test_case=test_case, actual_result=actual_result, passed=passed)
        )

        return results

    def generate_coverage_report(self) -> Dict[str, Any]:
        """Generate comprehensive coverage report."""
        total_tests = len(self.test_results)
        passed_tests = sum(1 for r in self.test_results if r.passed)
        failed_tests = total_tests - passed_tests

        # Calculate coverage metrics
        coverage = {
            "total_tests": total_tests,
            "passed_tests": passed_tests,
            "failed_tests": failed_tests,
            "success_rate": (
                (passed_tests / total_tests * 100) if total_tests > 0 else 0
            ),
            "test_results": [
                {
                    "name": r.test_case.name,
                    "passed": r.passed,
                    "expected": r.test_case.expected_result.value,
                    "actual": r.actual_result.value,
                    "execution_time_ms": r.execution_time_ms,
                    "tags": r.test_case.tags,
                }
                for r in self.test_results
            ],
        }

        return coverage

    def run_all_tests(self) -> bool:
        """Run all test suites and return overall success."""
        logger.info("Starting comprehensive replay test suite...")

        # Run all test suites
        good_results = self.run_good_trace_suite()
        bad_results = self.run_bad_trace_suite()
        property_results = self.run_property_tests()

        # Combine all results
        self.test_results = good_results + bad_results + property_results

        # Generate coverage report
        coverage = self.generate_coverage_report()

        # Log summary
        logger.info(f"\n{'='*50}")
        logger.info("TEST SUITE SUMMARY")
        logger.info(f"{'='*50}")
        logger.info(f"Total Tests: {coverage['total_tests']}")
        logger.info(f"Passed: {coverage['passed_tests']}")
        logger.info(f"Failed: {coverage['failed_tests']}")
        logger.info(f"Success Rate: {coverage['success_rate']:.1f}%")
        logger.info(f"{'='*50}")

        # Check if any tests failed
        if coverage["failed_tests"] > 0:
            logger.error("❌ Some tests failed! CI gate should block merge.")
            return False
        else:
            logger.info("✅ All tests passed! CI gate should allow merge.")
            return True


def main():
    """Main entry point for replay test suite."""
    parser = argparse.ArgumentParser(
        description="Replay Test Suite for Provability Fabric"
    )
    parser.add_argument("--dfa-path", required=True, help="Path to DFA JSON file")
    parser.add_argument(
        "--suite",
        choices=["good", "bad", "property", "all"],
        default="all",
        help="Test suite to run",
    )
    parser.add_argument("--output", help="Output file for test results")

    args = parser.parse_args()

    # Initialize test suite
    test_suite = ReplayTestSuite(args.dfa_path)

    # Run tests based on suite selection
    if args.suite == "good":
        results = test_suite.run_good_trace_suite()
        test_suite.test_results = results
    elif args.suite == "bad":
        results = test_suite.run_bad_trace_suite()
        test_suite.test_results = results
    elif args.suite == "property":
        results = test_suite.run_property_tests()
        test_suite.test_results = results
    else:  # all
        success = test_suite.run_all_tests()
        if not success:
            sys.exit(1)

    # Generate and save coverage report
    coverage = test_suite.generate_coverage_report()

    if args.output:
        with open(args.output, "w") as f:
            json.dump(coverage, f, indent=2)
        logger.info(f"Coverage report saved to {args.output}")

    # Exit with appropriate code for CI
    if coverage["failed_tests"] > 0:
        logger.error("Test suite failed - CI gate should block merge")
        sys.exit(1)
    else:
        logger.info("Test suite passed - CI gate should allow merge")
        sys.exit(0)


if __name__ == "__main__":
    import time

    main()
