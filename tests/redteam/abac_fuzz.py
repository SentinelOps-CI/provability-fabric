#!/usr/bin/env python3
"""
ABAC Fuzz Testing for Cross-Tenant Isolation

This is a fixture-bound HTTP probe for the Rust retrieval gateway. The
independent reference corpus and explicit positive/negative controls prevent
empty-index or malformed-response runs from earning a success verdict.
The current server's token verifier is not cryptographically complete.
"""

import asyncio
import json
import random
import string
import time
from typing import TYPE_CHECKING, Dict, List, Tuple, Optional
import hashlib
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor
import logging
import os

from retrieval_contract import inspect_query_response, load_reference_documents

from observation_gate import observation_failures

if TYPE_CHECKING:
    import aiohttp

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class TestCase:
    """Represents a single ABAC test case"""

    tenant: str
    subject_id: str
    subject_roles: List[str]
    query: str
    expected_labels: List[str]
    expected_tenant: str
    test_id: str
    denial_reason: Optional[str] = None


@dataclass
class TestResult:
    """Represents the result of a test case"""

    test_case: TestCase
    success: bool
    error_message: Optional[str]
    response_time_ms: float
    result_count: int
    cross_tenant_leak: bool
    unauthorized_access: bool
    denial_observed: bool = False


class ABACFuzzTester:
    """Comprehensive ABAC fuzz tester"""

    def __init__(
        self,
        base_url: str,
        max_workers: int = 10,
        *,
        capability_token: str,
        reference_documents: Dict[str, Dict],
        seed: int = 42,
    ):
        if not capability_token or not reference_documents:
            raise ValueError("live retrieval probes need a token and an independent reference corpus")
        self.base_url = base_url
        self.max_workers = max_workers
        self.capability_token = capability_token
        self.reference_documents = reference_documents
        self.rng = random.Random(seed)
        self.test_cases: List[TestCase] = []
        self.results: List[TestResult] = []

        self.tenants = sorted({doc["tenant"] for doc in reference_documents.values()})

        self.roles = [
            "admin",
            "user",
            "guest",
            "analyst",
            "manager",
            "auditor",
            "developer",
            "support",
            "finance",
            "hr",
            "legal",
            "security",
        ]

        self.labels = [
            "public",
            "private",
            "confidential",
            "secret",
            "financial",
            "pii",
            "internal",
            "external",
            "sensitive",
            "restricted",
            "classified",
            "top-secret",
            "for-your-eyes-only",
            "need-to-know",
            "compartmented",
            "special-access",
            "unclassified",
            "declassified",
            "draft",
            "final",
        ]

        # Enhanced test scenarios
        self.attack_scenarios = [
            "privilege_escalation",
            "role_confusion",
            "label_manipulation",
            "tenant_hopping",
            "session_hijacking",
            "capability_injection",
            "context_confusion",
            "boundary_violation",
        ]

        # Advanced role combinations
        self.role_combinations = [
            ["admin", "user"],
            ["admin", "guest"],
            ["user", "analyst"],
            ["manager", "finance"],
            ["auditor", "security"],
            ["developer", "support"],
            ["hr", "legal"],
            ["admin", "user", "analyst"],
            ["manager", "finance", "hr"],
            ["auditor", "security", "legal"],
        ]

        # Malicious query patterns
        self.malicious_patterns = [
            "SELECT * FROM",
            "UNION SELECT",
            "OR 1=1",
            "'; DROP TABLE",
            "OR 'admin'='admin",
            "UNION ALL SELECT",
            "OR '1'='1'--",
            "OR 'x'='x",
        ]

        self.query_templates = [
            "find documents about {topic}",
            "search for {topic} in {label} data",
            "retrieve {label} information for {subject}",
            "get {label} records from {date}",
            "query {label} database for {term}",
            "extract {label} data containing {pattern}",
            "analyze {label} content with {criteria}",
            "filter {label} results by {condition}",
        ]

        self.topics = [
            "budget",
            "revenue",
            "expenses",
            "customers",
            "employees",
            "projects",
            "contracts",
            "policies",
            "reports",
            "meetings",
            "strategies",
            "compliance",
            "security",
            "performance",
            "quality",
        ]

    def generate_test_case(self) -> TestCase:
        """Generate a random test case"""
        tenant = self.rng.choice(self.tenants)
        subject_id = f"user_{self.rng.randint(1000, 9999)}"
        subject_roles = self.rng.sample(self.roles, self.rng.randint(1, 3))

        # Generate query
        template = self.rng.choice(self.query_templates)
        topic = self.rng.choice(self.topics)
        label = self.rng.choice(self.labels)
        query = template.format(
            topic=topic,
            label=label,
            subject=subject_id,
            date=f"2024-{self.rng.randint(1, 12):02d}",
            term=self.rng.choice(self.topics),
            pattern=f"pattern_{self.rng.randint(1, 100)}",
            criteria=f"criteria_{self.rng.randint(1, 50)}",
            condition=f"condition_{self.rng.randint(1, 25)}",
        )

        # Roles are workload metadata: the Rust API does not accept role claims.
        # The requested label filter is the actual wire-level input.
        expected_labels = [label]
        expected_tenant = tenant

        test_id = hashlib.sha256(f"{tenant}:{subject_id}:{query}".encode()).hexdigest()[
            :16
        ]

        return TestCase(
            tenant=tenant,
            subject_id=subject_id,
            subject_roles=subject_roles,
            query=query,
            expected_labels=expected_labels,
            expected_tenant=expected_tenant,
            test_id=test_id,
        )

    def generate_test_cases(self, count: int = 100000) -> None:
        """Construct explicit per-tenant controls and reproducible fuzz workload."""
        minimum = 3 * len(self.tenants)
        if count < minimum:
            raise ValueError(f"at least {minimum} probes needed for per-tenant controls")
        self.test_cases = []
        for tenant in self.tenants:
            # A positive control needs an independently seeded public document.
            self.test_cases.append(TestCase(
                tenant=tenant, subject_id="user_fixture", subject_roles=["user"],
                query="reference corpus", expected_labels=["public"],
                expected_tenant=tenant, test_id=f"{tenant}-positive-public",
            ))
            # These negative controls test input-presence and the explicit
            # secret-label denial. They do not validate cryptographic tokens.
            self.test_cases.append(TestCase(
                tenant=tenant, subject_id="user_fixture", subject_roles=["user"],
                query="reference corpus", expected_labels=["public"],
                expected_tenant=tenant, test_id=f"{tenant}-empty-token",
                denial_reason="empty_token",
            ))
            self.test_cases.append(TestCase(
                tenant=tenant, subject_id="user_fixture", subject_roles=["user"],
                query="reference corpus", expected_labels=["secret"],
                expected_tenant=tenant, test_id=f"{tenant}-secret-label",
                denial_reason="secret_label",
            ))
        while len(self.test_cases) < count:
            self.test_cases.append(self.generate_test_case())
        logger.info("Prepared %d probes with explicit controls", len(self.test_cases))

    async def execute_test_case(
        self, session: "aiohttp.ClientSession", test_case: TestCase
    ) -> TestResult:
        """Run a declared HTTP probe against the current Rust /query protocol."""
        start_time = time.monotonic()
        token = "" if test_case.denial_reason == "empty_token" else self.capability_token
        payload = {
            "query": test_case.query,
            "tenant": test_case.tenant,
            "subject_id": test_case.subject_id,
            "capability_token": token,
            "labels_filter": test_case.expected_labels,
            "limit": 10,
        }
        try:
            async with session.post(
                f"{self.base_url.rstrip('/')}/query",
                json=payload,
                headers={"Content-Type": "application/json"},
            ) as response:
                elapsed_ms = (time.monotonic() - start_time) * 1000
                if test_case.denial_reason:
                    if response.status != 403:
                        detail = (await response.text())[:240]
                        raise ValueError(
                            f"expected HTTP 403 for {test_case.denial_reason}, "
                            f"observed {response.status}: {detail}"
                        )
                    return TestResult(
                        test_case=test_case, success=True, error_message=None,
                        response_time_ms=elapsed_ms, result_count=0,
                        cross_tenant_leak=False, unauthorized_access=False,
                        denial_observed=True,
                    )
                if response.status != 200:
                    detail = (await response.text())[:240]
                    raise ValueError(f"HTTP {response.status}: {detail}")
                data = await response.json()
                count, cross_tenant, unauthorized = inspect_query_response(
                    data,
                    expected_tenant=test_case.expected_tenant,
                    expected_subject=test_case.subject_id,
                    requested_labels=test_case.expected_labels,
                    known_documents=self.reference_documents,
                )
                return TestResult(
                    test_case=test_case, success=True, error_message=None,
                    response_time_ms=elapsed_ms, result_count=count,
                    cross_tenant_leak=cross_tenant, unauthorized_access=unauthorized,
                )
        except Exception as exc:
            return TestResult(
                test_case=test_case, success=False, error_message=str(exc),
                response_time_ms=(time.monotonic() - start_time) * 1000,
                result_count=0, cross_tenant_leak=False, unauthorized_access=False,
            )

    async def run_fuzz_tests(self) -> None:
        """Run all fuzz tests"""
        import aiohttp

        logger.info("Starting ABAC fuzz tests...")

        connector = aiohttp.TCPConnector(limit=self.max_workers)
        timeout = aiohttp.ClientTimeout(total=30)

        async with aiohttp.ClientSession(
            connector=connector, timeout=timeout
        ) as session:
            # Execute tests in batches
            batch_size = 1000
            total_batches = (len(self.test_cases) + batch_size - 1) // batch_size

            for batch_num in range(total_batches):
                start_idx = batch_num * batch_size
                end_idx = min(start_idx + batch_size, len(self.test_cases))
                batch_cases = self.test_cases[start_idx:end_idx]

                logger.info(
                    f"Executing batch {batch_num + 1}/{total_batches} "
                    f"({len(batch_cases)} test cases)"
                )

                # Execute batch concurrently
                tasks = [
                    self.execute_test_case(session, test_case)
                    for test_case in batch_cases
                ]

                batch_results = await asyncio.gather(*tasks, return_exceptions=True)

                # Process results
                for result in batch_results:
                    if isinstance(result, TestResult):
                        self.results.append(result)
                    else:
                        logger.error(f"Test execution failed: {result}")

                # Check for violations
                violations = [
                    r
                    for r in batch_results
                    if isinstance(r, TestResult)
                    and (r.cross_tenant_leak or r.unauthorized_access)
                ]

                if violations:
                    logger.error(
                        f"Found {len(violations)} violations in batch {batch_num + 1}"
                    )
                    for violation in violations:
                        logger.error(f"Violation: {violation.test_case.test_id}")

    def generate_report(self) -> Dict:
        """Generate comprehensive test report"""
        total_tests = len(self.results)
        successful_tests = len([r for r in self.results if r.success])
        failed_tests = total_tests - successful_tests

        cross_tenant_leaks = len([r for r in self.results if r.cross_tenant_leak])
        unauthorized_accesses = len([r for r in self.results if r.unauthorized_access])

        avg_response_time = (
            sum(r.response_time_ms for r in self.results) / total_tests
            if total_tests > 0
            else 0
        )

        # Group results by tenant
        tenant_results = {}
        for result in self.results:
            tenant = result.test_case.tenant
            if tenant not in tenant_results:
                tenant_results[tenant] = []
            tenant_results[tenant].append(result)

        # Group results by role
        role_results = {}
        for result in self.results:
            for role in result.test_case.subject_roles:
                if role not in role_results:
                    role_results[role] = []
                role_results[role].append(result)

        report = {
            "summary": {
                "total_tests": total_tests,
                "successful_tests": successful_tests,
                "failed_tests": failed_tests,
                "success_rate": (
                    (successful_tests / total_tests * 100) if total_tests > 0 else 0
                ),
                "cross_tenant_leaks": cross_tenant_leaks,
                "unauthorized_accesses": unauthorized_accesses,
                "avg_response_time_ms": avg_response_time,
            },
            "violations": {
                "cross_tenant_leaks": cross_tenant_leaks,
                "unauthorized_accesses": unauthorized_accesses,
                "total_violations": cross_tenant_leaks + unauthorized_accesses,
            },
            "tenant_breakdown": {
                tenant: {
                    "total": len(results),
                    "successful": len([r for r in results if r.success]),
                    "violations": len(
                        [
                            r
                            for r in results
                            if r.cross_tenant_leak or r.unauthorized_access
                        ]
                    ),
                }
                for tenant, results in tenant_results.items()
            },
            "role_breakdown": {
                role: {
                    "total": len(results),
                    "successful": len([r for r in results if r.success]),
                    "violations": len(
                        [
                            r
                            for r in results
                            if r.cross_tenant_leak or r.unauthorized_access
                        ]
                    ),
                }
                for role, results in role_results.items()
            },
        }

        observed_documents = sum(r.result_count for r in self.results if r.success)
        problems = observation_failures(
            planned=len(self.test_cases),
            recorded=total_tests,
            valid_responses=successful_tests,
            positive_controls=observed_documents,
            violations=cross_tenant_leaks + unauthorized_accesses,
        )
        for tenant in self.tenants:
            if not any(
                r.success and not r.test_case.denial_reason
                and r.test_case.tenant == tenant and r.result_count > 0
                for r in self.results
            ):
                problems.append(f"no seeded positive document observed for tenant {tenant}")
            for denial_reason in ("empty_token", "secret_label"):
                if not any(
                    r.success and r.denial_observed
                    and r.test_case.tenant == tenant
                    and r.test_case.denial_reason == denial_reason
                    for r in self.results
                ):
                    problems.append(
                        f"missing observed {denial_reason} negative control for tenant {tenant}"
                    )
        report["execution"] = {
            "planned_requests": len(self.test_cases),
            "observed_responses": total_tests,
            "valid_responses": successful_tests,
            "document_observations": observed_documents,
            "observed_denials": sum(r.denial_observed for r in self.results),
            "reference_documents": len(self.reference_documents),
            "test_tenants": list(self.tenants),
            "status": "FAIL" if problems else "PASS",
            "failures": problems,
        }

        return report

    def save_results(self, filename: str) -> None:
        """Save test results to file"""
        report = self.generate_report()

        with open(filename, "w") as f:
            json.dump(report, f, indent=2)

        logger.info(f"Results saved to {filename}")


async def main():
    """Main function"""
    import argparse

    parser = argparse.ArgumentParser(description="ABAC Fuzz Testing")
    parser.add_argument(
        "--base-url",
        default="http://localhost:8080",
        help="Base URL for the retrieval gateway",
    )
    parser.add_argument(
        "--test-count",
        type=int,
        default=100000,
        help="Number of test cases to generate",
    )
    parser.add_argument(
        "--max-workers", type=int, default=10, help="Maximum concurrent workers"
    )
    parser.add_argument(
        "--output", default="abac_fuzz_results.json", help="Output file for results"
    )
    parser.add_argument(
        "--queries",
        type=int,
        default=None,
        help="Alias for --test-count (compatibility with make security)",
    )
    parser.add_argument(
        "--offline",
        action="store_true",
        help="Validate harness setup without calling a live retrieval gateway",
    )
    parser.add_argument(
        "--fixture-manifest",
        help="Independent JSON reference manifest for a pre-seeded, disposable corpus",
    )
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument(
        "--token-env", default="PF_RETRIEVAL_CAPABILITY_TOKEN",
        help="Environment variable containing a disposable test capability token",
    )

    args = parser.parse_args()
    test_count = args.queries if args.queries is not None else args.test_count
    if test_count <= 0:
        parser.error('the number of test queries must be positive')

    if args.offline:
        print(f"Offline ABAC fuzz validation ({test_count} planned queries)")
        print("Harness setup only: no live gateway requests or security verdict")
        return

    # A trusted reference manifest must be supplied independently of the
    # service's own response. Never infer an oracle from a returned document.
    if not args.fixture_manifest:
        parser.error("--fixture-manifest is mandatory for live retrieval tests")
    try:
        reference_documents = load_reference_documents(args.fixture_manifest)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        parser.error(f"invalid fixture manifest: {exc}")
    capability_token = os.environ.get(args.token_env, "")
    if not capability_token:
        parser.error(f"missing disposable capability token in {args.token_env}")
    tester = ABACFuzzTester(
        args.base_url,
        args.max_workers,
        capability_token=capability_token,
        reference_documents=reference_documents,
        seed=args.seed,
    )
    try:
        tester.generate_test_cases(test_count)
    except ValueError as exc:
        parser.error(str(exc))

    # Run tests
    await tester.run_fuzz_tests()

    # Generate and save report
    tester.save_results(args.output)

    # Print summary
    report = tester.generate_report()
    summary = report["summary"]
    violations = report["violations"]

    print(f"\n=== ABAC Fuzz Test Results ===")
    print(f"Total Tests: {summary['total_tests']}")
    print(f"Successful: {summary['successful_tests']} ({summary['success_rate']:.2f}%)")
    print(f"Failed: {summary['failed_tests']}")
    print(f"Cross-Tenant Leaks: {violations['cross_tenant_leaks']}")
    print(f"Unauthorized Accesses: {violations['unauthorized_accesses']}")
    print(f"Total Violations: {violations['total_violations']}")
    print(f"Average Response Time: {summary['avg_response_time_ms']:.2f}ms")

    # A zero-leak count is meaningful only for a complete observed execution.
    problems = report["execution"]["failures"]
    if problems:
        print("\nFAILED: ABAC observations are incomplete or violated:")
        for problem in problems:
            print(f"  - {problem}")
        raise SystemExit(1)
    print("\nObserved ABAC probes completed without recorded violations.")
    print("Tenant isolation still needs known seeded cross-tenant fixtures and negative controls.")


if __name__ == "__main__":
    asyncio.run(main())
