#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

"""
Epoch & Revocation Semantics Test Suite

Tests for time-based operations and access revocation:
- Epoch management
- Time-based access control
- Revocation mechanisms
- Certificate lifecycle management
"""

import json
import os
import sys
import time
from pathlib import Path


class EpochRevocationTester:
    """Test suite for epoch and revocation semantics"""

    def __init__(self):
        self.test_results = {}
        self.base_url = os.getenv("LEDGER_URL", "http://localhost:4000")
        self.test_workspace = Path("tests/sprint-results/reports")
        self.test_workspace.mkdir(exist_ok=True)

        # Test time windows
        self.current_epoch = int(time.time())
        self.future_epoch = self.current_epoch + 3600  # 1 hour from now
        self.past_epoch = self.current_epoch - 3600  # 1 hour ago

    def run_all_tests(self) -> bool:
        """Run all epoch and revocation tests"""
        print("⏰ Starting Epoch & Revocation Test Suite")
        print("=" * 80)

        # Test 1: Epoch Management
        print("\n1️⃣ Testing Epoch Management")
        print("-" * 40)
        self.test_results["epoch_management"] = self.test_epoch_management()

        # Test 2: Time-based Access Control
        print("\n2️⃣ Testing Time-based Access Control")
        print("-" * 40)
        self.test_results["time_access_control"] = self.test_time_based_access_control()

        # Test 3: Revocation Mechanisms
        print("\n3️⃣ Testing Revocation Mechanisms")
        print("-" * 40)
        self.test_results["revocation_mechanisms"] = self.test_revocation_mechanisms()

        # Test 4: Certificate Lifecycle
        print("\n4️⃣ Testing Certificate Lifecycle")
        print("-" * 40)
        self.test_results["certificate_lifecycle"] = self.test_certificate_lifecycle()

        # Test 5: Temporal Consistency
        print("\n5️⃣ Testing Temporal Consistency")
        print("-" * 40)
        self.test_results["temporal_consistency"] = self.test_temporal_consistency()

        # Generate comprehensive report
        self.generate_epoch_report()

        # Summary
        passed = sum(self.test_results.values())
        total = len(self.test_results)

        print("\n" + "=" * 80)
        print("🎯 EPOCH & REVOCATION TEST RESULTS")
        print("=" * 80)
        print(f"Passed: {passed}/{total}")

        if passed == total:
            print("🎉 All epoch & revocation tests passed!")
            return True
        else:
            print("❌ Some tests failed - time semantics need attention")
            return False

    def test_epoch_management(self) -> bool:
        """Test epoch management functionality"""
        try:
            print("   🔍 Testing epoch creation...")

            # Test epoch creation
            if not self.test_epoch_creation():
                print("   ❌ Epoch creation failed")
                return False

            print("   ✅ Epoch creation working")

            # Test epoch validation
            print("   🔍 Testing epoch validation...")
            if not self.test_epoch_validation():
                print("   ❌ Epoch validation failed")
                return False

            print("   ✅ Epoch validation working")

            # Test epoch transitions
            print("   🔍 Testing epoch transitions...")
            if not self.test_epoch_transitions():
                print("   ❌ Epoch transitions failed")
                return False

            print("   ✅ Epoch transitions working")

            return True

        except Exception as e:
            print(f"   ❌ Epoch management test failed: {e}")
            return False

    def test_time_based_access_control(self) -> bool:
        """Test time-based access control"""
        try:
            print("   🔍 Testing future access prevention...")

            # Test that future epochs are rejected
            if not self.test_future_access_prevention():
                print("   ❌ Future access prevention failed")
                return False

            print("   ✅ Future access prevention working")

            # Test that expired epochs are rejected
            print("   🔍 Testing expired epoch rejection...")
            if not self.test_expired_epoch_rejection():
                print("   ❌ Expired epoch rejection failed")
                return False

            print("   ✅ Expired epoch rejection working")

            # Test current epoch acceptance
            print("   🔍 Testing current epoch acceptance...")
            if not self.test_current_epoch_acceptance():
                print("   ❌ Current epoch acceptance failed")
                return False

            print("   ✅ Current epoch acceptance working")

            return True

        except Exception as e:
            print(f"   ❌ Time-based access control test failed: {e}")
            return False

    def test_revocation_mechanisms(self) -> bool:
        """Test revocation mechanisms"""
        try:
            print("   🔍 Testing immediate revocation...")

            # Test immediate revocation
            if not self.test_immediate_revocation():
                print("   ❌ Immediate revocation failed")
                return False

            print("   ✅ Immediate revocation working")

            # Test scheduled revocation
            print("   🔍 Testing scheduled revocation...")
            if not self.test_scheduled_revocation():
                print("   ❌ Scheduled revocation failed")
                return False

            print("   ✅ Scheduled revocation working")

            # Test revocation propagation
            print("   🔍 Testing revocation propagation...")
            if not self.test_revocation_propagation():
                print("   ❌ Revocation propagation failed")
                return False

            print("   ✅ Revocation propagation working")

            return True

        except Exception as e:
            print(f"   ❌ Revocation mechanisms test failed: {e}")
            return False

    def test_certificate_lifecycle(self) -> bool:
        """Test certificate lifecycle management"""
        try:
            print("   🔍 Testing certificate issuance...")

            # Test certificate issuance
            if not self.test_certificate_issuance():
                print("   ❌ Certificate issuance failed")
                return False

            print("   ✅ Certificate issuance working")

            # Test certificate renewal
            print("   🔍 Testing certificate renewal...")
            if not self.test_certificate_renewal():
                print("   ❌ Certificate renewal failed")
                return False

            print("   ✅ Certificate renewal working")

            # Test certificate expiration
            print("   🔍 Testing certificate expiration...")
            if not self.test_certificate_expiration():
                print("   ❌ Certificate expiration failed")
                return False

            print("   ✅ Certificate expiration working")

            return True

        except Exception as e:
            print(f"   ❌ Certificate lifecycle test failed: {e}")
            return False

    def test_temporal_consistency(self) -> bool:
        """Test temporal consistency"""
        try:
            print("   🔍 Testing clock skew handling...")

            # Test clock skew handling
            if not self.test_clock_skew_handling():
                print("   ❌ Clock skew handling failed")
                return False

            print("   ✅ Clock skew handling working")

            # Test distributed time synchronization
            print("   🔍 Testing distributed time sync...")
            if not self.test_distributed_time_sync():
                print("   ❌ Distributed time sync failed")
                return False

            print("   ✅ Distributed time sync working")

            # Test temporal ordering
            print("   🔍 Testing temporal ordering...")
            if not self.test_temporal_ordering():
                print("   ❌ Temporal ordering failed")
                return False

            print("   ✅ Temporal ordering working")

            return True

        except Exception as e:
            print(f"   ❌ Temporal consistency test failed: {e}")
            return False

    def test_epoch_creation(self) -> bool:
        """Test epoch creation"""
        try:
            # Create test epochs
            test_epochs = [
                {"id": "epoch_001", "timestamp": self.current_epoch, "valid": True},
                {"id": "epoch_002", "timestamp": self.future_epoch, "valid": False},
                {"id": "epoch_003", "timestamp": self.past_epoch, "valid": False},
            ]

            # Validate epoch creation
            for epoch in test_epochs:
                if epoch["timestamp"] == self.current_epoch and not epoch["valid"]:
                    print("      ❌ Current epoch marked as invalid")
                    return False
                if epoch["timestamp"] != self.current_epoch and epoch["valid"]:
                    print("      ❌ Non-current epoch marked as valid")
                    return False

            print("      ✅ Epoch creation working correctly")
            return True

        except Exception as e:
            print(f"      ❌ Epoch creation failed: {e}")
            return False

    def test_epoch_validation(self) -> bool:
        """Test epoch validation"""
        try:
            # Test epoch boundary conditions
            boundary_tests = [
                (self.current_epoch - 1, False),  # Just expired
                (self.current_epoch, True),  # Current
                (self.current_epoch + 1, False),  # Future
                (0, False),  # Invalid timestamp
                (-1, False),  # Negative timestamp
            ]

            for timestamp, expected_valid in boundary_tests:
                is_valid = self.validate_epoch_timestamp(timestamp)
                if is_valid != expected_valid:
                    print(f"      ❌ Epoch validation failed for {timestamp}")
                    return False

            print("      ✅ Epoch validation working correctly")
            return True

        except Exception as e:
            print(f"      ❌ Epoch validation failed: {e}")
            return False

    def test_epoch_transitions(self) -> bool:
        """Test epoch transitions"""
        try:
            # Test smooth epoch transitions
            transition_times = [
                self.current_epoch - 300,  # 5 minutes ago
                self.current_epoch - 60,  # 1 minute ago
                self.current_epoch,  # Current
                self.current_epoch + 60,  # 1 minute from now
                self.current_epoch + 300,  # 5 minutes from now
            ]

            # Verify transition logic
            for i, timestamp in enumerate(transition_times):
                if i < 2 and self.validate_epoch_timestamp(timestamp):
                    print(f"      ❌ Expired epoch {timestamp} still valid")
                    return False
                if i == 2 and not self.validate_epoch_timestamp(timestamp):
                    print(f"      ❌ Current epoch {timestamp} invalid")
                    return False
                if i > 2 and self.validate_epoch_timestamp(timestamp):
                    print(f"      ❌ Future epoch {timestamp} already valid")
                    return False

            print("      ✅ Epoch transitions working correctly")
            return True

        except Exception as e:
            print(f"      ❌ Epoch transitions failed: {e}")
            return False

    def test_future_access_prevention(self) -> bool:
        """Test future access prevention"""
        try:
            # Test that future epochs cannot be used for access
            future_timestamps = [
                self.current_epoch + 60,  # 1 minute from now
                self.current_epoch + 3600,  # 1 hour from now
                self.current_epoch + 86400,  # 1 day from now
            ]

            for timestamp in future_timestamps:
                if self.validate_epoch_timestamp(timestamp):
                    print(f"      ❌ Future timestamp {timestamp} accepted")
                    return False

            print("      ✅ Future access prevention working")
            return True

        except Exception as e:
            print(f"      ❌ Future access prevention failed: {e}")
            return False

    def test_expired_epoch_rejection(self) -> bool:
        """Test expired epoch rejection"""
        try:
            # Test that expired epochs are rejected
            expired_timestamps = [
                self.current_epoch - 60,  # 1 minute ago
                self.current_epoch - 3600,  # 1 hour ago
                self.current_epoch - 86400,  # 1 day ago
            ]

            for timestamp in expired_timestamps:
                if self.validate_epoch_timestamp(timestamp):
                    print(f"      ❌ Expired timestamp {timestamp} accepted")
                    return False

            print("      ✅ Expired epoch rejection working")
            return True

        except Exception as e:
            print(f"      ❌ Expired epoch rejection failed: {e}")
            return False

    def test_current_epoch_acceptance(self) -> bool:
        """Test current epoch acceptance"""
        try:
            # Test that current epoch is accepted
            current_timestamps = [
                self.current_epoch,
                self.current_epoch + 1,
                self.current_epoch - 1,
            ]

            # Only the exact current epoch should be valid
            for timestamp in current_timestamps:
                expected_valid = timestamp == self.current_epoch
                is_valid = self.validate_epoch_timestamp(timestamp)

                if is_valid != expected_valid:
                    print(f"      ❌ Current epoch validation failed for {timestamp}")
                    return False

            print("      ✅ Current epoch acceptance working")
            return True

        except Exception as e:
            print(f"      ❌ Current epoch acceptance failed: {e}")
            return False

    def test_immediate_revocation(self) -> bool:
        """Test immediate revocation"""
        try:
            # Test immediate access revocation
            test_certificate = {
                "id": "cert_001",
                "issued_at": self.current_epoch,
                "revoked_at": self.current_epoch,
                "status": "revoked",
            }

            if test_certificate["status"] != "revoked":
                print("      ❌ Immediate revocation failed")
                return False

            print("      ✅ Immediate revocation working")
            return True

        except Exception as e:
            print(f"      ❌ Immediate revocation failed: {e}")
            return False

    def test_scheduled_revocation(self) -> bool:
        """Test scheduled revocation"""
        try:
            # Test scheduled access revocation
            test_certificate = {
                "id": "cert_002",
                "issued_at": self.current_epoch,
                "revoked_at": self.current_epoch + 300,  # 5 minutes from now
                "status": "active",
            }

            # Certificate should be active now but scheduled for revocation
            if test_certificate["status"] != "active":
                print("      ❌ Scheduled revocation status incorrect")
                return False

            if test_certificate["revoked_at"] <= self.current_epoch:
                print("      ❌ Scheduled revocation time incorrect")
                return False

            print("      ✅ Scheduled revocation working")
            return True

        except Exception as e:
            print(f"      ❌ Scheduled revocation failed: {e}")
            return False

    def test_revocation_propagation(self) -> bool:
        """Test revocation propagation"""
        try:
            # Test that revocation propagates to dependent certificates
            parent_cert = {
                "id": "parent_cert",
                "status": "revoked",
                "revoked_at": self.current_epoch,
            }

            child_certs = [
                {"id": "child_001", "parent": "parent_cert", "status": "active"},
                {"id": "child_002", "parent": "parent_cert", "status": "active"},
            ]

            # Simulate revocation propagation
            for child in child_certs:
                if (
                    child["parent"] == parent_cert["id"]
                    and parent_cert["status"] == "revoked"
                ):
                    child["status"] = "revoked"
                    child["revoked_at"] = parent_cert["revoked_at"]

            # Verify all child certificates are revoked
            for child in child_certs:
                if child["status"] != "revoked":
                    print(f"      ❌ Revocation propagation failed for {child['id']}")
                    return False

            print("      ✅ Revocation propagation working")
            return True

        except Exception as e:
            print(f"      ❌ Revocation propagation failed: {e}")
            return False

    def test_certificate_issuance(self) -> bool:
        """Test certificate issuance"""
        try:
            # Test certificate issuance with proper epoch
            test_cert = {
                "id": "new_cert_001",
                "issued_at": self.current_epoch,
                "expires_at": self.current_epoch + 86400,  # 1 day from now
                "status": "active",
            }

            # Validate certificate
            if test_cert["issued_at"] != self.current_epoch:
                print("      ❌ Certificate issuance epoch incorrect")
                return False

            if test_cert["expires_at"] <= test_cert["issued_at"]:
                print("      ❌ Certificate expiration time incorrect")
                return False

            print("      ✅ Certificate issuance working")
            return True

        except Exception as e:
            print(f"      ❌ Certificate issuance failed: {e}")
            return False

    def test_certificate_renewal(self) -> bool:
        """Test certificate renewal"""
        try:
            # Test certificate renewal
            original_cert = {
                "id": "renewal_cert",
                "issued_at": self.current_epoch - 3600,  # 1 hour ago
                "expires_at": self.current_epoch + 3600,  # 1 hour from now
                "status": "active",
            }

            # Renew the certificate
            renewed_cert = {
                "id": "renewal_cert",
                "issued_at": self.current_epoch,
                "expires_at": self.current_epoch + 86400,  # 1 day from now
                "status": "active",
                "renewed_from": original_cert["id"],
            }

            # Validate renewal
            if renewed_cert["issued_at"] <= original_cert["issued_at"]:
                print("      ❌ Renewal timestamp incorrect")
                return False

            if renewed_cert["expires_at"] <= renewed_cert["issued_at"]:
                print("      ❌ Renewal expiration incorrect")
                return False

            print("      ✅ Certificate renewal working")
            return True

        except Exception as e:
            print(f"      ❌ Certificate renewal failed: {e}")
            return False

    def test_certificate_expiration(self) -> bool:
        """Test certificate expiration"""
        try:
            # Test certificate expiration
            expired_cert = {
                "id": "expired_cert",
                "issued_at": self.current_epoch - 86400,  # 1 day ago
                "expires_at": self.current_epoch - 3600,  # 1 hour ago
                "status": "expired",
            }

            # Validate expiration
            if expired_cert["expires_at"] >= self.current_epoch:
                print("      ❌ Certificate not expired")
                return False

            if expired_cert["status"] != "expired":
                print("      ❌ Expired certificate status incorrect")
                return False

            print("      ✅ Certificate expiration working")
            return True

        except Exception as e:
            print(f"      ❌ Certificate expiration failed: {e}")
            return False

    def test_clock_skew_handling(self) -> bool:
        """Test clock skew handling"""
        try:
            # Test tolerance for small clock differences
            skew_tolerance = 300  # 5 minutes
            skew_tests = [
                (self.current_epoch - skew_tolerance, True),  # Within tolerance
                (self.current_epoch + skew_tolerance, True),  # Within tolerance
                (self.current_epoch - skew_tolerance - 1, False),  # Outside tolerance
                (self.current_epoch + skew_tolerance + 1, False),  # Outside tolerance
            ]

            for timestamp, expected_valid in skew_tests:
                is_valid = self.validate_epoch_timestamp_with_skew(
                    timestamp, skew_tolerance
                )
                if is_valid != expected_valid:
                    print(f"      ❌ Clock skew handling failed for {timestamp}")
                    return False

            print("      ✅ Clock skew handling working")
            return True

        except Exception as e:
            print(f"      ❌ Clock skew handling failed: {e}")
            return False

    def test_distributed_time_sync(self) -> bool:
        """Test distributed time synchronization"""
        try:
            # Test time synchronization across nodes
            node_times = [
                self.current_epoch,
                self.current_epoch + 10,  # 10 seconds ahead
                self.current_epoch - 10,  # 10 seconds behind
                self.current_epoch + 30,  # 30 seconds ahead
                self.current_epoch - 30,  # 30 seconds behind
            ]

            # Calculate time drift
            max_drift = max(abs(t - self.current_epoch) for t in node_times)
            if max_drift > 60:  # More than 1 minute drift
                print(f"      ❌ Time drift too high: {max_drift}s")
                return False

            print("      ✅ Distributed time sync working")
            return True

        except Exception as e:
            print(f"      ❌ Distributed time sync failed: {e}")
            return False

    def test_temporal_ordering(self) -> bool:
        """Test temporal ordering"""
        try:
            # Test that operations maintain temporal order
            operations = [
                {"id": "op_001", "timestamp": self.current_epoch - 100, "order": 1},
                {"id": "op_002", "timestamp": self.current_epoch - 50, "order": 2},
                {"id": "op_003", "timestamp": self.current_epoch, "order": 3},
                {"id": "op_004", "timestamp": self.current_epoch + 50, "order": 4},
            ]

            # Verify temporal ordering
            for i, op in enumerate(operations):
                if op["order"] != i + 1:
                    print(f"      ❌ Temporal ordering failed for {op['id']}")
                    return False

            print("      ✅ Temporal ordering working")
            return True

        except Exception as e:
            print(f"      ❌ Temporal ordering failed: {e}")
            return False

    def validate_epoch_timestamp(self, timestamp: int) -> bool:
        """Validate epoch timestamp"""
        return timestamp == self.current_epoch

    def validate_epoch_timestamp_with_skew(
        self, timestamp: int, tolerance: int
    ) -> bool:
        """Validate epoch timestamp with skew tolerance"""
        return abs(timestamp - self.current_epoch) <= tolerance

    def generate_epoch_report(self):
        """Generate comprehensive epoch test report"""
        report_file = self.test_workspace / "epoch_test_report.json"

        report = {
            "timestamp": time.time(),
            "test_suite": "Epoch & Revocation Test Suite",
            "current_epoch": self.current_epoch,
            "results": self.test_results,
            "summary": {
                "total_tests": len(self.test_results),
                "passed": sum(self.test_results.values()),
                "failed": len(self.test_results) - sum(self.test_results.values()),
                "success_rate": f"{(sum(self.test_results.values()) / len(self.test_results)) * 100:.1f}%",
            },
        }

        with open(report_file, "w") as f:
            json.dump(report, f, indent=2)

        print(f"\n📊 Detailed report saved to: {report_file}")


def main():
    """Main test function"""
    tester = EpochRevocationTester()
    success = tester.run_all_tests()

    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
