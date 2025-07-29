#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

import requests
import json
import time
import sys


def test_tenant_isolation():
    """Test tenant isolation and RBAC functionality"""

    base_url = "http://localhost:4000"

    # Test JWT tokens (simulated)
    tenant_a_token = "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0.eyJzdWIiOiJ0ZXN0LXVzZXItYSIsInRpZCI6InRlbmFudC1hIiwiaWF0IjoxNTE2MjM5MDIyfQ.test"
    tenant_b_token = "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0.eyJzdWIiOiJ0ZXN0LXVzZXItYiIsInRpZCI6InRlbmFudC1iIiwiaWF0IjoxNTE2MjM5MDIyfQ.test"

    headers_a = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {tenant_a_token}",
    }

    headers_b = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {tenant_b_token}",
    }

    print("🧪 Testing tenant isolation...")

    # Test 1: Tenant A creates a capsule
    print("1. Tenant A creating capsule...")
    create_query = {
        "query": """
        mutation {
            createCapsule(hash: "test-capsule-a", specSig: "test-sig-a", riskScore: 0.5) {
                id
                hash
                tenantId
            }
        }
        """
    }

    response = requests.post(
        f"{base_url}/graphql", headers=headers_a, json=create_query
    )

    if response.status_code != 200:
        print(f"❌ Failed to create capsule: {response.status_code}")
        return False

    print("✅ Tenant A capsule created successfully")

    # Test 2: Tenant B tries to access Tenant A's capsule (should fail)
    print("2. Testing tenant isolation - Tenant B accessing Tenant A's capsule...")
    query_a_capsule = {
        "query": """
        query {
            capsule(hash: "test-capsule-a") {
                id
                hash
                tenantId
            }
        }
        """
    }

    response = requests.post(
        f"{base_url}/graphql", headers=headers_b, json=query_a_capsule
    )

    if response.status_code in [200, 201]:
        print(
            "❌ Tenant isolation failed - Tenant B was able to access Tenant A's capsule"
        )
        return False

    print("✅ Tenant isolation working correctly")

    # Test 3: SQL injection prevention
    print("3. Testing SQL injection prevention...")
    injection_token = "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0.eyJzdWIiOiJ0ZXN0LXVzZXItYSIsInRpZCI6InRlbmFudC1hJy1VTklPTi1TRUxFQ1QtMSIsImlhdCI6MTUxNjIzOTAyMn0.test"

    headers_injection = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {injection_token}",
    }

    response = requests.post(
        f"{base_url}/graphql",
        headers=headers_injection,
        json={"query": "query { capsules { id hash } }"},
    )

    if response.status_code in [200, 201]:
        print("❌ SQL injection prevention failed")
        return False

    print("✅ SQL injection prevention working correctly")

    # Test 4: Invalid tenant rejection
    print("4. Testing invalid tenant rejection...")
    invalid_token = "eyJhbGciOiJSUzI1NiIsInR5cCI6IkpXVCIsImtpZCI6InRlc3Qta2V5In0.eyJzdWIiOiJ0ZXN0LXVzZXItaW52YWxpZCIsInRpZCI6ImludmFsaWQtdGVuYW50IiwiaWF0IjoxNTE2MjM5MDIyfQ.test"

    headers_invalid = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {invalid_token}",
    }

    response = requests.post(
        f"{base_url}/graphql",
        headers=headers_invalid,
        json={"query": "query { capsules { id hash } }"},
    )

    if response.status_code in [200, 201]:
        print("❌ Invalid tenant rejection failed")
        return False

    print("✅ Invalid tenant rejection working correctly")

    print("🎉 All RBAC tests passed!")
    return True


if __name__ == "__main__":
    # Wait for service to be ready
    print("⏳ Waiting for ledger service to be ready...")
    time.sleep(10)

    success = test_tenant_isolation()
    sys.exit(0 if success else 1)
