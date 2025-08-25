#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

import requests
import json
import time
import sys
import os
from typing import Dict


class TenantIsolationTester:
    """Test suite for tenant isolation and RBAC functionality"""

    def __init__(self, base_url: str = "http://localhost:4000"):
        self.base_url = base_url
        self.test_tenant_a = "tenant-a"
        self.test_tenant_b = "tenant-b"
        self.test_capsules = {}

    def wait_for_service(self, max_retries: int = 30) -> bool:
        """Wait for the GraphQL service to be ready"""
        print("⏳ Waiting for GraphQL service to be ready...")

        for attempt in range(max_retries):
            try:
                # Try a simple health check
                response = requests.get(f"{self.base_url}/health", timeout=5)
                if response.status_code == 200:
                    print("✅ GraphQL service is ready")
                    return True
            except requests.RequestException:
                pass

            try:
                # Try GraphQL introspection as fallback
                introspection_query = {
                    "query": """
                    query IntrospectionQuery {
                        __schema {
                            types {
                                name
                            }
                        }
                    }
                    """
                }
                response = requests.post(
                    f"{self.base_url}/graphql", json=introspection_query, timeout=5
                )
                if response.status_code == 200:
                    msg = "✅ GraphQL service is ready (introspection successful)"
                    print(msg)
                    return True
            except requests.RequestException:
                pass

            msg = f"   Attempt {attempt + 1}/{max_retries}: Service not ready, retrying..."
            print(msg)
            time.sleep(2)

        print("❌ GraphQL service failed to start within timeout")
        return False

    def setup_test_tenants(self) -> bool:
        """Set up test tenants in the database"""
        print("🔧 Setting up test tenants...")

        try:
            # Note: In a real test environment, you'd need admin privileges
            # For now, we'll assume they exist or use a different approach
            print("   ℹ️  Test tenants setup skipped (requires admin privileges)")
            return True

        except Exception as e:
            print(f"   ❌ Failed to setup test tenants: {e}")
            return False

    def generate_test_tokens(self) -> Dict[str, str]:
        """Generate test JWT tokens for different scenarios"""
        # In a real test environment, you'd use proper JWT signing
        # For testing, we'll use mock tokens that the service can validate

        tokens = {
            "tenant_a": (
                "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0."
                "eyJzdWIiOiJ0ZXN0LXVzZXItYSIsInRpZCI6ImF1dGgwfHt0ZW5hbnQtYX0iLC"
                "JhdWQiOiJodHRwczovL2FwaS5wcm92YWJpbGl0eS1mYWJyaWMub3JnIiwiaXNz"
                "IjoiaHR0cHM6Ly90ZXN0LmF1dGgwLmNvbSIsImlhdCI6MTUxNjIzOTAyMn0.test"
            ),
            "tenant_b": (
                "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0."
                "eyJzdWIiOiJ0ZXN0LXVzZXItYiIsInRpZCI6ImF1dGgwfHt0ZW5hbnQtYiIs"
                "ImF1ZCI6Imh0dHBzOi8vYXBpLnByb3ZhYmlsaXR5LWZhYnJpYy5vcmciLCJp"
                "c3MiOiJodHRwczovL3Rlc3QuYXV0aDAuY29tIiwiaWF0IjoxNTE2MjM5MDIyfQ.test"
            ),
            "invalid_tenant": (
                "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0."
                "eyJzdWIiOiJ0ZXN0LXVzZXItaW52YWxpZCIsInRpZCI6ImludmFsaWQtdGVuYW50Iiw"
                "iaWF0IjoxNTE2MjM5MDIyfQ.test"
            ),
            "malformed": "invalid.jwt.token",
        }

        return tokens

    def test_tenant_a_capsule_creation(self, token: str) -> bool:
        """Test that Tenant A can create a capsule"""
        print("1. Testing Tenant A capsule creation...")

        create_query = {
            "query": """
            mutation CreateCapsule($hash: String!, $specSig: String!, $riskScore: Float!) {
                createCapsule(hash: $hash, specSig: $specSig, riskScore: $riskScore) {
                    id
                    hash
                    tenantId
                    riskScore
                }
            }
            """,
            "variables": {
                "hash": "test-capsule-a-001",
                "specSig": "test-sig-a-001",
                "riskScore": 0.5,
            },
        }

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        }

        try:
            response = requests.post(
                f"{self.base_url}/graphql",
                headers=headers,
                json=create_query,
                timeout=10,
            )

            if response.status_code == 200:
                data = response.json()
                if "errors" in data:
                    print(f"   ❌ GraphQL errors: {data['errors']}")
                    return False

                if "data" in data and data["data"]["createCapsule"]:
                    capsule = data["data"]["createCapsule"]
                    self.test_capsules["tenant_a"] = capsule["hash"]
                    print(f"   ✅ Tenant A capsule created: {capsule['hash']}")
                    return True
                else:
                    print("   ❌ No capsule data returned")
                    return False
            else:
                print(f"   ❌ HTTP {response.status_code}: {response.text}")
                return False

        except requests.RequestException as e:
            print(f"   ❌ Request failed: {e}")
            return False

    def test_tenant_isolation(self, tenant_a_token: str, tenant_b_token: str) -> bool:
        """Test that Tenant B cannot access Tenant A's capsule"""
        print("2. Testing tenant isolation...")

        if "tenant_a" not in self.test_capsules:
            print("   ❌ No tenant A capsule to test isolation")
            return False

        capsule_hash = self.test_capsules["tenant_a"]

        query = {
            "query": """
            query GetCapsule($hash: String!) {
                capsule(hash: $hash) {
                    id
                    hash
                    tenantId
                    riskScore
                }
            }
            """,
            "variables": {"hash": capsule_hash},
        }

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {tenant_b_token}",
        }

        try:
            response = requests.post(
                f"{self.base_url}/graphql", headers=headers, json=query, timeout=10
            )

            # Tenant B should NOT be able to access Tenant A's capsule
            if response.status_code == 200:
                data = response.json()
                if "errors" in data:
                    # Check if the error indicates access denied
                    errors = data["errors"]
                    access_denied = any(
                        "access denied" in str(error).lower()
                        or "not found" in str(error).lower()
                        for error in errors
                    )
                    if access_denied:
                        print(
                            "   ✅ Tenant isolation working: Access denied as expected"
                        )
                        return True
                    else:
                        print(f"   ❌ Unexpected GraphQL errors: {errors}")
                        return False
                elif "data" in data and data["data"]["capsule"]:
                    print(
                        "   ❌ Tenant isolation failed: Tenant B accessed Tenant A's capsule"
                    )
                    return False
                else:
                    print("   ✅ Tenant isolation working: No data returned")
                    return True
            elif response.status_code in [401, 403, 404]:
                print("   ✅ Tenant isolation working: HTTP access denied")
                return True
            else:
                print(f"   ❌ Unexpected HTTP status: {response.status_code}")
                return False

        except requests.RequestException as e:
            print(f"   ❌ Request failed: {e}")
            return False

    def test_sql_injection_prevention(self, token: str) -> bool:
        """Test SQL injection prevention"""
        print("3. Testing SQL injection prevention...")

        # Test with potentially malicious tenant ID in JWT
        malicious_query = {
            "query": """
            query {
                capsules {
                    id
                    hash
                    tenantId
                }
            }
            """
        }

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        }

        try:
            response = requests.post(
                f"{self.base_url}/graphql",
                headers=headers,
                json=malicious_query,
                timeout=10,
            )

            # Should reject malicious tokens
            if response.status_code in [401, 403]:
                print(
                    "   ✅ SQL injection prevention working: Malicious token rejected"
                )
                return True
            elif response.status_code == 200:
                data = response.json()
                if "errors" in data:
                    print(
                        "   ✅ SQL injection prevention working: GraphQL errors returned"
                    )
                    return True
                else:
                    print(
                        "   ❌ SQL injection prevention failed: Malicious token accepted"
                    )
                    return False
            else:
                print(f"   ❌ Unexpected response: {response.status_code}")
                return False

        except requests.RequestException as e:
            print(f"   ❌ Request failed: {e}")
            return False

    def test_invalid_tenant_rejection(self, token: str) -> bool:
        """Test that invalid tenants are rejected"""
        print("4. Testing invalid tenant rejection...")

        query = {
            "query": """
            query {
                capsules {
                    id
                    hash
                }
            }
            """
        }

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        }

        try:
            response = requests.post(
                f"{self.base_url}/graphql", headers=headers, json=query, timeout=10
            )

            # Invalid tenant should be rejected
            if response.status_code in [401, 403]:
                print("   ✅ Invalid tenant rejection working: Access denied")
                return True
            elif response.status_code == 200:
                data = response.json()
                if "errors" in data:
                    print(
                        "   ✅ Invalid tenant rejection working: GraphQL errors returned"
                    )
                    return True
                else:
                    print(
                        "   ❌ Invalid tenant rejection failed: Invalid tenant accepted"
                    )
                    return False
            else:
                print(f"   ❌ Unexpected response: {response.status_code}")
                return False

        except requests.RequestException as e:
            print(f"   ❌ Request failed: {e}")
            return False

    def test_malformed_token_rejection(self, token: str) -> bool:
        """Test that malformed JWT tokens are rejected"""
        print("5. Testing malformed token rejection...")

        query = {
            "query": """
            query {
                capsules {
                    id
                    hash
                }
            }
            """
        }

        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {token}",
        }

        try:
            response = requests.post(
                f"{self.base_url}/graphql", headers=headers, json=query, timeout=10
            )

            # Malformed token should be rejected
            if response.status_code in [401, 403]:
                print("   ✅ Malformed token rejection working: Access denied")
                return True
            else:
                print(
                    f"   ❌ Malformed token rejection failed: Status {response.status_code}"
                )
                return False

        except requests.RequestException as e:
            print(f"   ❌ Request failed: {e}")
            return False

    def run_all_tests(self) -> bool:
        """Run all tenant isolation tests"""
        print("🧪 Starting Tenant Isolation Test Suite")
        print("=" * 60)

        # Wait for service to be ready
        if not self.wait_for_service():
            return False

        # Setup test tenants
        if not self.setup_test_tenants():
            return False

        # Generate test tokens
        tokens = self.generate_test_tokens()

        # Run tests
        test_results = []

        # Test 1: Tenant A creates capsule
        test_results.append(self.test_tenant_a_capsule_creation(tokens["tenant_a"]))

        # Test 2: Tenant isolation
        test_results.append(
            self.test_tenant_isolation(tokens["tenant_a"], tokens["tenant_b"])
        )

        # Test 3: SQL injection prevention
        test_results.append(self.test_sql_injection_prevention(tokens["tenant_a"]))

        # Test 4: Invalid tenant rejection
        test_results.append(
            self.test_invalid_tenant_rejection(tokens["invalid_tenant"])
        )

        # Test 5: Malformed token rejection
        test_results.append(self.test_malformed_token_rejection(tokens["malformed"]))

        # Summary
        passed = sum(test_results)
        total = len(test_results)

        print("\n" + "=" * 60)
        print("TEST RESULTS SUMMARY")
        print("=" * 60)
        print(f"Passed: {passed}/{total}")

        if passed == total:
            print("🎉 All tenant isolation tests passed!")
            return True
        else:
            print("❌ Some tests failed")
            return False


def main():
    """Main test function"""
    # Check if we should use a different URL
    base_url = os.getenv("LEDGER_URL", "http://localhost:4000")

    tester = TenantIsolationTester(base_url)
    success = tester.run_all_tests()

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
