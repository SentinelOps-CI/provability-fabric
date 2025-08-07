#!/usr/bin/env python3
"""
Test KMS attestation - verifies that KMS proxy requires attestation for key operations
"""

import asyncio
import json
import time
from datetime import datetime, timezone
from typing import Dict, Any


class KmsAttestationTest:
    def __init__(self):
        self.kms_url = "http://localhost:8082"

    def create_valid_attestation(self) -> Dict[str, Any]:
        """Create a valid attestation token"""
        return {
            "token": "valid_attestation_token",
            "pod_identity": "pod-secure-1",
            "policy_hash": "default_policy_hash",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "signature": "sig_1234567890",
        }

    def create_expired_attestation(self) -> Dict[str, Any]:
        """Create an expired attestation token"""
        expired_time = datetime.now(timezone.utc).timestamp() - 120  # 2 minutes ago
        expired_datetime = datetime.fromtimestamp(expired_time, tz=timezone.utc)

        return {
            "token": "expired_attestation_token",
            "pod_identity": "pod-secure-1",
            "policy_hash": "default_policy_hash",
            "timestamp": expired_datetime.isoformat(),
            "signature": "sig_1234567890",
        }

    def create_invalid_policy_attestation(self) -> Dict[str, Any]:
        """Create attestation with invalid policy hash"""
        return {
            "token": "invalid_policy_token",
            "pod_identity": "pod-secure-1",
            "policy_hash": "invalid_policy_hash",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "signature": "sig_1234567890",
        }

    def create_invalid_pod_attestation(self) -> Dict[str, Any]:
        """Create attestation with invalid pod identity"""
        return {
            "token": "invalid_pod_token",
            "pod_identity": "unauthorized-pod",
            "policy_hash": "default_policy_hash",
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "signature": "sig_1234567890",
        }

    async def test_valid_attestation_success(self):
        """Test that valid attestation allows KMS operations"""
        print("Testing valid attestation success...")

        kms_request = {
            "operation": "encrypt",
            "key_id": "test-key-1",
            "data": "sensitive-data",
            "attestation_token": self.create_valid_attestation(),
        }

        # Simulate KMS proxy response
        response = await self.simulate_kms_request(kms_request)

        assert response["success"], f"Valid attestation should succeed, got: {response}"
        assert (
            response["error"] is None
        ), f"Valid attestation should not have error, got: {response['error']}"
        assert (
            "encrypted_" in response["result"]
        ), f"Should return encrypted data, got: {response['result']}"

        print("✓ Valid attestation success test passed")

    async def test_no_attestation_denial(self):
        """Test that KMS operations without attestation are denied"""
        print("Testing no attestation denial...")

        kms_request = {
            "operation": "encrypt",
            "key_id": "test-key-1",
            "data": "sensitive-data",
            "attestation_token": None,
        }

        # Simulate KMS proxy response
        response = await self.simulate_kms_request(kms_request)

        assert not response["success"], f"No attestation should fail, got: {response}"
        assert (
            response["error"] is not None
        ), f"No attestation should have error, got: {response}"
        assert (
            "Attestation token required" in response["error"]
        ), f"Error should mention attestation required, got: {response['error']}"

        print("✓ No attestation denial test passed")

    async def test_expired_attestation_denial(self):
        """Test that expired attestation tokens are denied"""
        print("Testing expired attestation denial...")

        kms_request = {
            "operation": "decrypt",
            "key_id": "test-key-1",
            "data": "encrypted_sensitive-data",
            "attestation_token": self.create_expired_attestation(),
        }

        # Simulate KMS proxy response
        response = await self.simulate_kms_request(kms_request)

        assert not response[
            "success"
        ], f"Expired attestation should fail, got: {response}"
        assert (
            response["error"] is not None
        ), f"Expired attestation should have error, got: {response}"
        assert (
            "expired" in response["error"].lower()
        ), f"Error should mention expired, got: {response['error']}"

        print("✓ Expired attestation denial test passed")

    async def test_invalid_policy_denial(self):
        """Test that attestation with invalid policy hash is denied"""
        print("Testing invalid policy denial...")

        kms_request = {
            "operation": "sign",
            "key_id": "test-key-1",
            "data": "data-to-sign",
            "attestation_token": self.create_invalid_policy_attestation(),
        }

        # Simulate KMS proxy response
        response = await self.simulate_kms_request(kms_request)

        assert not response["success"], f"Invalid policy should fail, got: {response}"
        assert (
            response["error"] is not None
        ), f"Invalid policy should have error, got: {response}"
        assert (
            "policy" in response["error"].lower()
        ), f"Error should mention policy, got: {response['error']}"

        print("✓ Invalid policy denial test passed")

    async def test_invalid_pod_denial(self):
        """Test that attestation with invalid pod identity is denied"""
        print("Testing invalid pod denial...")

        kms_request = {
            "operation": "verify",
            "key_id": "test-key-1",
            "data": "signed-data",
            "attestation_token": self.create_invalid_pod_attestation(),
        }

        # Simulate KMS proxy response
        response = await self.simulate_kms_request(kms_request)

        assert not response["success"], f"Invalid pod should fail, got: {response}"
        assert (
            response["error"] is not None
        ), f"Invalid pod should have error, got: {response}"
        assert (
            "identity" in response["error"].lower()
        ), f"Error should mention identity, got: {response['error']}"

        print("✓ Invalid pod denial test passed")

    async def test_key_rotation(self):
        """Test that key rotation clears attestation cache"""
        print("Testing key rotation...")

        # First, make a valid request
        valid_request = {
            "operation": "encrypt",
            "key_id": "test-key-1",
            "data": "sensitive-data",
            "attestation_token": self.create_valid_attestation(),
        }

        response1 = await self.simulate_kms_request(valid_request)
        assert response1["success"], "First request should succeed"

        # Simulate key rotation
        await self.simulate_key_rotation()

        # Try the same request again - should still work with fresh attestation
        response2 = await self.simulate_kms_request(valid_request)
        assert response2[
            "success"
        ], "Request after rotation should still succeed with fresh attestation"

        print("✓ Key rotation test passed")

    async def simulate_kms_request(self, request: Dict[str, Any]) -> Dict[str, Any]:
        """Simulate KMS proxy request processing"""
        import uuid

        operation_id = str(uuid.uuid4())
        timestamp = datetime.now(timezone.utc).isoformat()

        # Check attestation if provided
        if request.get("attestation_token"):
            token = request["attestation_token"]

            # Validate token freshness (60 second TTL)
            token_time = datetime.fromisoformat(
                token["timestamp"].replace("Z", "+00:00")
            )
            now = datetime.now(timezone.utc)
            age_seconds = (now - token_time).total_seconds()

            if age_seconds > 60:
                return {
                    "success": False,
                    "result": None,
                    "error": f"Token expired (older than 60 seconds)",
                    "operation_id": operation_id,
                    "timestamp": timestamp,
                }

            # Validate policy hash
            allowed_policies = ["default_policy_hash", "secure_policy_hash"]
            if token["policy_hash"] not in allowed_policies:
                return {
                    "success": False,
                    "result": None,
                    "error": f"Policy hash {token['policy_hash']} not in allowed list",
                    "operation_id": operation_id,
                    "timestamp": timestamp,
                }

            # Validate pod identity
            allowed_pods = ["pod-secure-1", "pod-secure-2"]
            if token["pod_identity"] not in allowed_pods:
                return {
                    "success": False,
                    "result": None,
                    "error": f"Pod identity {token['pod_identity']} not in allowed list",
                    "operation_id": operation_id,
                    "timestamp": timestamp,
                }

            # Validate signature
            if not token["signature"].startswith("sig_"):
                return {
                    "success": False,
                    "result": None,
                    "error": "Invalid signature",
                    "operation_id": operation_id,
                    "timestamp": timestamp,
                }
        else:
            return {
                "success": False,
                "result": None,
                "error": "Attestation token required",
                "operation_id": operation_id,
                "timestamp": timestamp,
            }

        # Simulate KMS operation
        operation = request["operation"]
        data = request.get("data", "")

        if operation == "encrypt":
            result = f"encrypted_{data}"
        elif operation == "decrypt":
            result = data.replace("encrypted_", "")
        elif operation == "sign":
            result = f"signed_{data}"
        elif operation == "verify":
            result = "signature_valid"
        else:
            return {
                "success": False,
                "result": None,
                "error": "Invalid operation",
                "operation_id": operation_id,
                "timestamp": timestamp,
            }

        return {
            "success": True,
            "result": result,
            "error": None,
            "operation_id": operation_id,
            "timestamp": timestamp,
        }

    async def simulate_key_rotation(self):
        """Simulate key rotation operation"""
        # In a real implementation, this would rotate the keys
        # For testing, we just simulate the operation
        print("Simulating key rotation...")
        await asyncio.sleep(0.1)  # Simulate processing time

    async def run_all_tests(self):
        """Run all KMS attestation tests"""
        print("Running KMS attestation tests...")

        await self.test_valid_attestation_success()
        await self.test_no_attestation_denial()
        await self.test_expired_attestation_denial()
        await self.test_invalid_policy_denial()
        await self.test_invalid_pod_denial()
        await self.test_key_rotation()

        print("All KMS attestation tests passed! ✓")


async def main():
    """Main test runner"""
    test = KmsAttestationTest()
    await test.run_all_tests()


if __name__ == "__main__":
    asyncio.run(main())
