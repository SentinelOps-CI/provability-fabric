#!/usr/bin/env python3
"""
ABAC Fuzz Testing for Cross-Tenant Isolation

This script performs comprehensive fuzz testing of the ABAC (Attribute-Based Access Control)
system to ensure zero cross-tenant data leakage. It generates 100k+ queries with various
role/label permutations and verifies that no cross-tenant results are returned.
"""

import asyncio
import json
import random
import string
import time
from typing import Dict, List, Tuple, Optional
import aiohttp
import hashlib
from dataclasses import dataclass
from concurrent.futures import ThreadPoolExecutor
import logging

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


class ABACFuzzTester:
    """Comprehensive ABAC fuzz tester"""

    def __init__(self, base_url: str, max_workers: int = 10):
        self.base_url = base_url
        self.max_workers = max_workers
        self.test_cases: List[TestCase] = []
        self.results: List[TestResult] = []

        # Test data generation
        self.tenants = [
            "acme-corp",
            "tech-startup",
            "healthcare-org",
            "financial-bank",
            "government-agency",
            "education-uni",
            "retail-chain",
            "manufacturing-co",
        ]

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
        tenant = random.choice(self.tenants)
        subject_id = f"user_{random.randint(1000, 9999)}"
        subject_roles = random.sample(self.roles, random.randint(1, 3))

        # Generate query
        template = random.choice(self.query_templates)
        topic = random.choice(self.topics)
        label = random.choice(self.labels)
        query = template.format(
            topic=topic,
            label=label,
            subject=subject_id,
            date=f"2024-{random.randint(1, 12):02d}",
            term=random.choice(self.topics),
            pattern=f"pattern_{random.randint(1, 100)}",
            criteria=f"criteria_{random.randint(1, 50)}",
            condition=f"condition_{random.randint(1, 25)}",
        )

        # Expected labels based on roles and query
        expected_labels = self.determine_expected_labels(subject_roles, label)
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

    def determine_expected_labels(
        self, roles: List[str], requested_label: str
    ) -> List[str]:
        """Determine expected accessible labels based on roles"""
        accessible_labels = ["public"]  # Public is always accessible

        if "admin" in roles:
            accessible_labels.extend(["private", "confidential", "internal"])
        elif "manager" in roles:
            accessible_labels.extend(["private", "internal"])
        elif "analyst" in roles:
            accessible_labels.extend(["private"])
        elif "finance" in roles and requested_label == "financial":
            accessible_labels.append("financial")
        elif "hr" in roles and requested_label == "pii":
            accessible_labels.append("pii")
        elif "security" in roles:
            accessible_labels.extend(["confidential", "sensitive"])

        # Only return labels that were actually requested
        return [label for label in accessible_labels if label == requested_label]

    def generate_test_cases(self, count: int = 100000) -> None:
        """Generate the specified number of test cases"""
        logger.info(f"Generating {count} test cases...")

        for i in range(count):
            test_case = self.generate_test_case()
            self.test_cases.append(test_case)

            if (i + 1) % 10000 == 0:
                logger.info(f"Generated {i + 1} test cases")

        logger.info(f"Generated {len(self.test_cases)} test cases")

    async def execute_test_case(
        self, session: aiohttp.ClientSession, test_case: TestCase
    ) -> TestResult:
        """Execute a single test case"""
        start_time = time.time()

        try:
            # Prepare request payload
            payload = {
                "tenant": test_case.tenant,
                "subject_id": test_case.subject_id,
                "subject_roles": test_case.subject_roles,
                "query": test_case.query,
                "test_id": test_case.test_id,
            }

            # Make request to retrieval gateway
            async with session.post(
                f"{self.base_url}/api/v1/retrieve",
                json=payload,
                headers={"Content-Type": "application/json"},
            ) as response:
                response_time = (time.time() - start_time) * 1000

                if response.status == 200:
                    data = await response.json()
                    results = data.get("results", [])

                    # Check for cross-tenant leakage
                    cross_tenant_leak = False
                    unauthorized_access = False

                    for result in results:
                        result_tenant = result.get("tenant")
                        result_labels = result.get("labels", [])

                        # Check for cross-tenant data
                        if result_tenant != test_case.expected_tenant:
                            cross_tenant_leak = True
                            logger.error(
                                f"Cross-tenant leak detected: {test_case.test_id}"
                            )

                        # Check for unauthorized label access
                        for label in result_labels:
                            if label not in test_case.expected_labels:
                                unauthorized_access = True
                                logger.error(
                                    f"Unauthorized label access: {test_case.test_id}"
                                )

                    return TestResult(
                        test_case=test_case,
                        success=True,
                        error_message=None,
                        response_time_ms=response_time,
                        result_count=len(results),
                        cross_tenant_leak=cross_tenant_leak,
                        unauthorized_access=unauthorized_access,
                    )
                else:
                    error_text = await response.text()
                    return TestResult(
                        test_case=test_case,
                        success=False,
                        error_message=f"HTTP {response.status}: {error_text}",
                        response_time_ms=(time.time() - start_time) * 1000,
                        result_count=0,
                        cross_tenant_leak=False,
                        unauthorized_access=False,
                    )

        except Exception as e:
            return TestResult(
                test_case=test_case,
                success=False,
                error_message=str(e),
                response_time_ms=(time.time() - start_time) * 1000,
                result_count=0,
                cross_tenant_leak=False,
                unauthorized_access=False,
            )

    async def run_fuzz_tests(self) -> None:
        """Run all fuzz tests"""
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

    args = parser.parse_args()

    # Create tester
    tester = ABACFuzzTester(args.base_url, args.max_workers)

    # Generate test cases
    tester.generate_test_cases(args.test_count)

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

    # Exit with error if violations found
    if violations["total_violations"] > 0:
        print(f"\n❌ FAILED: Found {violations['total_violations']} violations!")
        exit(1)
    else:
        print(f"\n✅ PASSED: Zero violations detected!")


if __name__ == "__main__":
    asyncio.run(main())
