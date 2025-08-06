#!/usr/bin/env python3
"""
ABAC Fuzzing Test - Red team suite for testing tenant isolation and ABAC policies.

Generates 100k randomized queries across tenants/labels and expects 0 cross-tenant access.
Uses deterministic seeding for reproducible failure traces.
"""

import asyncio
import random
import string
import json
import time
import hashlib
from typing import List, Dict, Any, Tuple
import aiohttp
import argparse
from dataclasses import dataclass
from datetime import datetime


@dataclass
class FuzzQuery:
    """Represents a fuzzed query."""

    tenant: str
    subject_id: str
    query_text: str
    labels_filter: List[str]
    capability_token: str
    expected_allowed: bool
    cross_tenant_attempt: bool


@dataclass
class FuzzResult:
    """Result of a fuzz test."""

    query: FuzzQuery
    response_code: int
    response_data: Dict[str, Any]
    latency_ms: float
    error: str = ""


class ABACFuzzer:
    def __init__(self, gateway_url: str, seed: int = 42):
        self.gateway_url = gateway_url
        self.seed = seed
        random.seed(seed)

        # Test tenants and their data
        self.tenants = ["tenant_a", "tenant_b", "tenant_c", "tenant_d"]
        self.labels = ["public", "private", "confidential", "financial", "pii"]
        self.subjects = {
            "tenant_a": ["user_a1", "user_a2", "admin_a1"],
            "tenant_b": ["user_b1", "user_b2", "admin_b1"],
            "tenant_c": ["user_c1", "user_c2", "admin_c1"],
            "tenant_d": ["user_d1", "user_d2", "admin_d1"],
        }

        # Results tracking
        self.results: List[FuzzResult] = []
        self.violations: List[FuzzResult] = []

    def generate_queries(self, count: int) -> List[FuzzQuery]:
        """Generate randomized fuzz queries."""
        queries = []

        for i in range(count):
            # 80% legitimate queries, 20% cross-tenant attempts
            cross_tenant = random.random() < 0.2

            if cross_tenant:
                # Cross-tenant attack: user from one tenant tries to access another
                attacking_tenant = random.choice(self.tenants)
                target_tenant = random.choice(
                    [t for t in self.tenants if t != attacking_tenant]
                )

                query = FuzzQuery(
                    tenant=target_tenant,  # Target tenant's data
                    subject_id=random.choice(
                        self.subjects[attacking_tenant]
                    ),  # Attacker's subject
                    query_text=self.generate_query_text(),
                    labels_filter=random.sample(self.labels, k=random.randint(1, 3)),
                    capability_token=self.generate_fake_token(attacking_tenant),
                    expected_allowed=False,  # Should be denied
                    cross_tenant_attempt=True,
                )
            else:
                # Legitimate query within tenant
                tenant = random.choice(self.tenants)
                query = FuzzQuery(
                    tenant=tenant,
                    subject_id=random.choice(self.subjects[tenant]),
                    query_text=self.generate_query_text(),
                    labels_filter=random.sample(self.labels, k=random.randint(1, 3)),
                    capability_token=self.generate_valid_token(tenant),
                    expected_allowed=True,
                    cross_tenant_attempt=False,
                )

            queries.append(query)

        return queries

    def generate_query_text(self) -> str:
        """Generate random query text."""
        query_templates = [
            "Find documents about {topic}",
            "Search for {entity} information",
            "Get data related to {keyword}",
            "Retrieve {document_type} files",
            "Show me {category} records",
        ]

        topics = [
            "financial reports",
            "user data",
            "system logs",
            "contracts",
            "policies",
        ]
        entities = ["customer information", "employee records", "transaction data"]
        keywords = ["compliance", "security", "performance", "audit"]
        document_types = ["configuration", "specification", "manual"]
        categories = ["sensitive", "public", "internal"]

        template = random.choice(query_templates)

        replacements = {
            "topic": random.choice(topics),
            "entity": random.choice(entities),
            "keyword": random.choice(keywords),
            "document_type": random.choice(document_types),
            "category": random.choice(categories),
        }

        for placeholder, value in replacements.items():
            template = template.replace(f"{{{placeholder}}}", value)

        return template

    def generate_valid_token(self, tenant: str) -> str:
        """Generate a valid-looking capability token for tenant."""
        token_data = {
            "tenant": tenant,
            "capabilities": ["read_docs", "basic_access"],
            "expires_at": int(time.time()) + 3600,
        }
        return f"valid_token_{hashlib.sha256(json.dumps(token_data).encode()).hexdigest()[:16]}"

    def generate_fake_token(self, tenant: str) -> str:
        """Generate a fake/invalid capability token."""
        return f"fake_token_{tenant}_{random.randint(1000, 9999)}"

    async def execute_query(
        self, session: aiohttp.ClientSession, query: FuzzQuery
    ) -> FuzzResult:
        """Execute a single fuzz query."""
        start_time = time.time()

        payload = {
            "query": query.query_text,
            "tenant": query.tenant,
            "subject_id": query.subject_id,
            "capability_token": query.capability_token,
            "labels_filter": query.labels_filter,
        }

        try:
            async with session.post(
                f"{self.gateway_url}/query",
                json=payload,
                timeout=aiohttp.ClientTimeout(total=30),
            ) as response:
                latency_ms = (time.time() - start_time) * 1000
                response_data = {}

                try:
                    response_data = await response.json()
                except:
                    response_data = {"error": "Invalid JSON response"}

                return FuzzResult(
                    query=query,
                    response_code=response.status,
                    response_data=response_data,
                    latency_ms=latency_ms,
                )

        except Exception as e:
            latency_ms = (time.time() - start_time) * 1000
            return FuzzResult(
                query=query,
                response_code=0,
                response_data={},
                latency_ms=latency_ms,
                error=str(e),
            )

    async def run_fuzz_test(
        self, query_count: int, concurrency: int = 50
    ) -> Dict[str, Any]:
        """Run the complete fuzz test."""
        print(
            f"🚀 Starting ABAC fuzz test with {query_count} queries (seed: {self.seed})"
        )

        # Generate queries
        queries = self.generate_queries(query_count)
        print(f"📋 Generated {len(queries)} queries")

        # Execute queries with concurrency control
        connector = aiohttp.TCPConnector(limit=concurrency)
        async with aiohttp.ClientSession(connector=connector) as session:

            semaphore = asyncio.Semaphore(concurrency)

            async def bounded_execute(query):
                async with semaphore:
                    return await self.execute_query(session, query)

            print(f"⚡ Executing queries with concurrency {concurrency}")
            start_time = time.time()

            self.results = await asyncio.gather(*[bounded_execute(q) for q in queries])

            total_time = time.time() - start_time

        # Analyze results
        analysis = self.analyze_results(total_time)

        return analysis

    def analyze_results(self, total_time: float) -> Dict[str, Any]:
        """Analyze fuzz test results for security violations."""
        print("🔍 Analyzing results for security violations...")

        # Track different types of violations
        cross_tenant_violations = []
        unauthorized_access = []
        response_time_violations = []
        error_analysis = {"timeouts": 0, "server_errors": 0, "other": 0}

        for result in self.results:
            # Check for cross-tenant access violations
            if result.query.cross_tenant_attempt and result.response_code == 200:
                cross_tenant_violations.append(result)

            # Check for unauthorized access that succeeded
            if not result.query.expected_allowed and result.response_code == 200:
                unauthorized_access.append(result)

            # Check response time SLO violations (p95 < 2s)
            if result.latency_ms > 2000:
                response_time_violations.append(result)

            # Categorize errors
            if result.error:
                if "timeout" in result.error.lower():
                    error_analysis["timeouts"] += 1
                elif result.response_code >= 500:
                    error_analysis["server_errors"] += 1
                else:
                    error_analysis["other"] += 1

        # Calculate statistics
        successful_queries = len([r for r in self.results if r.response_code == 200])
        denied_queries = len([r for r in self.results if r.response_code in [401, 403]])
        error_queries = len([r for r in self.results if r.response_code >= 400])

        latencies = [r.latency_ms for r in self.results if r.latency_ms > 0]
        latencies.sort()

        p50_latency = latencies[len(latencies) // 2] if latencies else 0
        p95_latency = latencies[int(len(latencies) * 0.95)] if latencies else 0
        p99_latency = latencies[int(len(latencies) * 0.99)] if latencies else 0

        analysis = {
            "summary": {
                "total_queries": len(self.results),
                "successful": successful_queries,
                "denied": denied_queries,
                "errors": error_queries,
                "total_time_s": total_time,
                "qps": len(self.results) / total_time if total_time > 0 else 0,
            },
            "security_violations": {
                "cross_tenant_violations": len(cross_tenant_violations),
                "unauthorized_access": len(unauthorized_access),
                "total_violations": len(cross_tenant_violations)
                + len(unauthorized_access),
            },
            "performance": {
                "p50_latency_ms": p50_latency,
                "p95_latency_ms": p95_latency,
                "p99_latency_ms": p99_latency,
                "slo_violations": len(response_time_violations),
            },
            "errors": error_analysis,
            "violation_details": {
                "cross_tenant": [
                    self.result_to_dict(r) for r in cross_tenant_violations[:10]
                ],
                "unauthorized": [
                    self.result_to_dict(r) for r in unauthorized_access[:10]
                ],
            },
        }

        # Store violations for detailed analysis
        self.violations = cross_tenant_violations + unauthorized_access

        return analysis

    def result_to_dict(self, result: FuzzResult) -> Dict[str, Any]:
        """Convert result to dictionary for JSON serialization."""
        return {
            "tenant": result.query.tenant,
            "subject_id": result.query.subject_id,
            "cross_tenant_attempt": result.query.cross_tenant_attempt,
            "response_code": result.response_code,
            "latency_ms": result.latency_ms,
            "error": result.error,
        }

    def save_detailed_report(self, analysis: Dict[str, Any], output_file: str):
        """Save detailed test report."""
        report = {
            "test_metadata": {
                "timestamp": datetime.utcnow().isoformat(),
                "seed": self.seed,
                "gateway_url": self.gateway_url,
                "test_type": "abac_fuzz",
            },
            "analysis": analysis,
            "violations": [self.result_to_dict(r) for r in self.violations],
        }

        with open(output_file, "w") as f:
            json.dump(report, f, indent=2)

        print(f"📄 Detailed report saved: {output_file}")


async def main():
    parser = argparse.ArgumentParser(description="ABAC Fuzzing Test")
    parser.add_argument(
        "--gateway-url", default="http://localhost:8080", help="Retrieval gateway URL"
    )
    parser.add_argument(
        "--queries", type=int, default=100000, help="Number of queries to generate"
    )
    parser.add_argument(
        "--concurrency", type=int, default=50, help="Concurrent requests"
    )
    parser.add_argument(
        "--seed", type=int, default=42, help="Random seed for reproducibility"
    )
    parser.add_argument(
        "--output", default="abac_fuzz_report.json", help="Output report file"
    )

    args = parser.parse_args()

    fuzzer = ABACFuzzer(args.gateway_url, args.seed)
    analysis = await fuzzer.run_fuzz_test(args.queries, args.concurrency)

    # Print summary
    print("\n" + "=" * 60)
    print("ABAC FUZZ TEST RESULTS")
    print("=" * 60)

    print(f"📊 Total Queries: {analysis['summary']['total_queries']}")
    print(f"✅ Successful: {analysis['summary']['successful']}")
    print(f"🚫 Denied: {analysis['summary']['denied']}")
    print(f"❌ Errors: {analysis['summary']['errors']}")
    print(f"⚡ QPS: {analysis['summary']['qps']:.2f}")

    print(f"\n🔒 SECURITY VIOLATIONS:")
    print(
        f"  Cross-tenant: {analysis['security_violations']['cross_tenant_violations']}"
    )
    print(f"  Unauthorized: {analysis['security_violations']['unauthorized_access']}")
    print(f"  Total: {analysis['security_violations']['total_violations']}")

    print(f"\n⚡ PERFORMANCE:")
    print(f"  P50 latency: {analysis['performance']['p50_latency_ms']:.2f}ms")
    print(f"  P95 latency: {analysis['performance']['p95_latency_ms']:.2f}ms")
    print(f"  P99 latency: {analysis['performance']['p99_latency_ms']:.2f}ms")
    print(f"  SLO violations: {analysis['performance']['slo_violations']}")

    # Save detailed report
    fuzzer.save_detailed_report(analysis, args.output)

    # Exit with error if violations found
    if analysis["security_violations"]["total_violations"] > 0:
        print("\n❌ CRITICAL: Security violations detected!")
        print("Review the detailed report for violation traces.")
        exit(1)
    elif analysis["performance"]["slo_violations"] > 0:
        print("\n⚠️  WARNING: Performance SLO violations detected!")
        exit(1)
    else:
        print("\n✅ ALL TESTS PASSED: No security violations detected!")
        exit(0)


if __name__ == "__main__":
    asyncio.run(main())
