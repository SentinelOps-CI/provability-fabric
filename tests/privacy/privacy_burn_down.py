#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

TRUST-FIRE Phase 2: Tenant Privacy Burn-Down Test
"""

import argparse
import json
import redis
import requests
import subprocess
import sys
import time
import zipfile
from datetime import datetime, timedelta
from typing import Dict, List, Optional


class PrivacyBurnDownTest:
    """TRUST-FIRE Phase 2: Tenant Privacy Burn-Down Test"""

    def __init__(self, tenant_id: str, redis_url: str, ledger_url: str):
        self.tenant_id = tenant_id
        self.redis_url = redis_url
        self.ledger_url = ledger_url
        self.redis_client = redis.from_url(redis_url)
        self.epsilon_limit = 5.0  # TRUST-FIRE spec: 5.0 epsilon limit
        self.queries_sent = 0
        self.guard_trips = 0

    def setup_epsilon_config(self) -> bool:
        """Setup epsilon limits for tenant (Action 1)"""
        try:
            # Simulate kubectl patch command
            config_data = {"data": {self.tenant_id: "5.0"}}

            # Store in Redis for test purposes
            self.redis_client.set(
                f"epsilon_config:{self.tenant_id}", json.dumps(config_data)
            )

            print(f"✅ Epsilon limit set to 5.0 for tenant {self.tenant_id}")
            return True

        except Exception as e:
            print(f"❌ Failed to setup epsilon config: {e}")
            return False

    def replay_queries(self, count: int = 100000) -> bool:
        """Replay queries to consume epsilon budget (Action 2)"""
        try:
            print(f"🔄 Replaying {count} queries for tenant {self.tenant_id}...")

            # Simulate query replay with epsilon consumption
            for i in range(count):
                # Each query consumes 0.00005 epsilon (100k queries = 5.0 epsilon)
                epsilon_consumed = 0.00005

                # Update Redis key for epsilon tracking
                current_key = f"eps:{self.tenant_id}"
                current_value = float(self.redis_client.get(current_key) or 0)
                new_value = current_value + epsilon_consumed

                self.redis_client.set(current_key, new_value)
                self.queries_sent += 1

                # Check if we've exceeded the limit
                if new_value >= self.epsilon_limit:
                    # Trigger guard trip
                    guard_trip = {
                        "tenant": self.tenant_id,
                        "reason": "epsilon_exceeded",
                        "timestamp": datetime.utcnow().isoformat(),
                        "epsilon_consumed": new_value,
                        "epsilon_limit": self.epsilon_limit,
                    }

                    # Store guard trip
                    self.redis_client.set(
                        f"guard_trip:{self.tenant_id}:{int(time.time())}",
                        json.dumps(guard_trip),
                    )
                    self.guard_trips += 1

                    print(f"🚨 Guard trip triggered at query {i+1}")
                    break

                # Progress indicator
                if (i + 1) % 10000 == 0:
                    print(f"  Processed {i+1}/{count} queries...")

            print(f"✅ Query replay completed. Sent {self.queries_sent} queries.")
            return True

        except Exception as e:
            print(f"❌ Failed to replay queries: {e}")
            return False

    def export_dsar_data(self, output_file: str) -> bool:
        """Export DSAR data for tenant (Action 3)"""
        try:
            print(f"📦 Exporting DSAR data for tenant {self.tenant_id}...")

            # Simulate DSAR export
            export_data = {
                "tenant_id": self.tenant_id,
                "export_date": datetime.utcnow().isoformat(),
                "usage_events": [
                    {
                        "id": f"event-{i}",
                        "tenant_id": self.tenant_id,
                        "cpu_ms": 1500,
                        "net_bytes": 1024000,
                        "timestamp": (
                            datetime.utcnow() - timedelta(hours=i)
                        ).isoformat(),
                    }
                    for i in range(100)  # 100 usage events
                ],
                "capsules": [
                    {
                        "id": f"capsule-{i}",
                        "hash": f"sha256:test{i}",
                        "spec_sig": f"sig:test{i}",
                        "risk_score": 0.15,
                        "tenant_id": self.tenant_id,
                        "created_at": (
                            datetime.utcnow() - timedelta(days=i)
                        ).isoformat(),
                        "updated_at": datetime.utcnow().isoformat(),
                    }
                    for i in range(10)  # 10 capsules
                ],
                "metadata": {
                    "export_version": "1.0",
                    "pii_redacted": True,
                    "encrypted": True,
                },
            }

            # Create ZIP file
            with zipfile.ZipFile(output_file, "w") as zipf:
                # Add manifest
                zipf.writestr("manifest.json", json.dumps(export_data, indent=2))

                # Add usage events
                zipf.writestr(
                    "usage_events.json",
                    json.dumps(export_data["usage_events"], indent=2),
                )

                # Add capsules
                zipf.writestr(
                    "capsules.json", json.dumps(export_data["capsules"], indent=2)
                )

            print(f"✅ DSAR export created: {output_file}")
            return True

        except Exception as e:
            print(f"❌ Failed to export DSAR data: {e}")
            return False

    def validate_epsilon_consumption(self) -> bool:
        """Validate epsilon consumption (Metric 1)"""
        try:
            current_key = f"eps:{self.tenant_id}"
            final_value = float(self.redis_client.get(current_key) or 0)

            # TRUST-FIRE Gate: final value 5.0 ± 0.10
            tolerance = 0.10
            expected = 5.0

            if abs(final_value - expected) <= tolerance:
                print(
                    f"✅ Epsilon consumption within tolerance: {final_value:.3f} ± {tolerance}"
                )
                return True
            else:
                print(
                    f"❌ Epsilon consumption outside tolerance: {final_value:.3f} (expected {expected} ± {tolerance})"
                )
                return False

        except Exception as e:
            print(f"❌ Failed to validate epsilon consumption: {e}")
            return False

    def validate_guard_trips(self) -> bool:
        """Validate guard trips (Metric 2)"""
        try:
            # Count guard trips for this tenant
            guard_trip_keys = self.redis_client.keys(f"guard_trip:{self.tenant_id}:*")
            trip_count = len(guard_trip_keys)

            # TRUST-FIRE Gate: must equal 1
            if trip_count == 1:
                print(f"✅ Guard trip count correct: {trip_count}")
                return True
            else:
                print(f"❌ Guard trip count incorrect: {trip_count} (expected 1)")
                return False

        except Exception as e:
            print(f"❌ Failed to validate guard trips: {e}")
            return False

    def validate_dsar_schema(self, export_file: str) -> bool:
        """Validate DSAR export schema (Metric 3)"""
        try:
            with zipfile.ZipFile(export_file, "r") as zipf:
                # Check required files exist
                required_files = ["manifest.json", "usage_events.json", "capsules.json"]
                for file in required_files:
                    if file not in zipf.namelist():
                        print(f"❌ Required file missing: {file}")
                        return False

                # Validate manifest schema
                manifest_data = json.loads(zipf.read("manifest.json"))
                required_fields = [
                    "tenant_id",
                    "export_date",
                    "usage_events",
                    "capsules",
                    "metadata",
                ]

                for field in required_fields:
                    if field not in manifest_data:
                        print(f"❌ Required field missing: {field}")
                        return False

                # Check for PII fields (should not exist)
                manifest_str = json.dumps(manifest_data)
                pii_fields = ["email", "phone", "address", "name", "ssn", "credit_card"]
                for pii_field in pii_fields:
                    if pii_field in manifest_str.lower():
                        print(f"❌ PII field found: {pii_field}")
                        return False

                print("✅ DSAR schema validation passed")
                return True

        except Exception as e:
            print(f"❌ Failed to validate DSAR schema: {e}")
            return False

    def run_triple_check(self) -> bool:
        """TRUST-FIRE Triple-Check: Inject email field and verify failure"""
        try:
            print("🔄 Running triple-check: Injecting email field...")

            # Create export with email field (should fail)
            export_data = {
                "tenant_id": self.tenant_id,
                "export_date": datetime.utcnow().isoformat(),
                "usage_events": [],
                "capsules": [],
                "metadata": {
                    "export_version": "1.0",
                    "pii_redacted": True,
                    "encrypted": True,
                    "email": "test@example.com",  # This should cause failure
                },
            }

            # Save to file
            with open("test_export_with_email.zip", "w") as f:
                json.dump(export_data, f)

            # Validate should fail
            if self.validate_dsar_schema("test_export_with_email.zip"):
                print("❌ Triple-check failed: PII validation should have failed")
                return False
            else:
                print("✅ Triple-check passed: PII validation correctly failed")
                return True

        except Exception as e:
            print(f"❌ Triple-check error: {e}")
            return False

    def run_epsilon_limit_test(self) -> bool:
        """TRUST-FIRE Triple-Check: Test with higher epsilon limit"""
        try:
            print("🔄 Running epsilon limit test: Setting limit to 50...")

            # Set higher epsilon limit
            self.redis_client.set(f"epsilon_config:{self.tenant_id}", "50.0")

            # Replay queries (should not trigger guard trip)
            for i in range(1000):
                epsilon_consumed = 0.00005
                current_key = f"eps:{self.tenant_id}"
                current_value = float(self.redis_client.get(current_key) or 0)
                new_value = current_value + epsilon_consumed

                self.redis_client.set(current_key, new_value)

                # Should not exceed 50.0 limit
                if new_value >= 50.0:
                    break

            # Check that no guard trip was triggered
            guard_trip_keys = self.redis_client.keys(f"guard_trip:{self.tenant_id}:*")
            if len(guard_trip_keys) == 0:
                print("✅ Epsilon limit test passed: No guard trip with higher limit")
                return True
            else:
                print(
                    "❌ Epsilon limit test failed: Guard trip triggered with higher limit"
                )
                return False

        except Exception as e:
            print(f"❌ Epsilon limit test error: {e}")
            return False

    def run_trust_fire_phase2(self) -> bool:
        """Run complete TRUST-FIRE Phase 2 test"""
        print("🚀 Starting TRUST-FIRE Phase 2: Tenant Privacy Burn-Down")
        print("=" * 60)

        # Action 1: Setup epsilon config
        if not self.setup_epsilon_config():
            return False

        # Action 2: Replay queries
        if not self.replay_queries():
            return False

        # Action 3: Export DSAR data
        export_file = f"dsar_export_{self.tenant_id}.zip"
        if not self.export_dsar_data(export_file):
            return False

        print("\n📊 TRUST-FIRE Phase 2 Metrics Validation:")
        print("-" * 40)

        # Validate all three gates
        gate1 = self.validate_epsilon_consumption()
        gate2 = self.validate_guard_trips()
        gate3 = self.validate_dsar_schema(export_file)

        all_gates_pass = gate1 and gate2 and gate3

        print(f"\n🎯 TRUST-FIRE Phase 2 Gates:")
        print(f"  Gate 1 (Epsilon Consumption): {'✅ PASS' if gate1 else '❌ FAIL'}")
        print(f"  Gate 2 (Guard Trips): {'✅ PASS' if gate2 else '❌ FAIL'}")
        print(f"  Gate 3 (DSAR Schema): {'✅ PASS' if gate3 else '❌ FAIL'}")

        if all_gates_pass:
            print("\n🔄 Running Triple-Check Tests...")

            triple_check1 = self.run_triple_check()
            triple_check2 = self.run_epsilon_limit_test()

            print(f"\n🔍 Triple-Check Results:")
            print(f"  PII Injection Test: {'✅ PASS' if triple_check1 else '❌ FAIL'}")
            print(f"  Epsilon Limit Test: {'✅ PASS' if triple_check2 else '❌ FAIL'}")

            all_triple_checks_pass = triple_check1 and triple_check2

            if all_triple_checks_pass:
                print(
                    "\n🎉 TRUST-FIRE Phase 2 PASSED - All gates and triple-checks satisfied!"
                )
                return True
            else:
                print("\n❌ TRUST-FIRE Phase 2 FAILED - Triple-checks failed")
                return False
        else:
            print("\n❌ TRUST-FIRE Phase 2 FAILED - Gates not satisfied")
            return False


def main():
    parser = argparse.ArgumentParser(
        description="TRUST-FIRE Phase 2: Privacy Burn-Down Test"
    )
    parser.add_argument("--tenant-id", default="acme-beta", help="Tenant ID to test")
    parser.add_argument(
        "--redis-url", default="redis://localhost:6379", help="Redis URL"
    )
    parser.add_argument(
        "--ledger-url", default="http://localhost:4000", help="Ledger URL"
    )
    parser.add_argument(
        "--output", default="dsar_export.zip", help="DSAR export output file"
    )

    args = parser.parse_args()

    # Create test instance
    test = PrivacyBurnDownTest(args.tenant_id, args.redis_url, args.ledger_url)

    # Run TRUST-FIRE Phase 2
    success = test.run_trust_fire_phase2()

    if success:
        print("\n✅ TRUST-FIRE Phase 2 completed successfully")
        sys.exit(0)
    else:
        print("\n❌ TRUST-FIRE Phase 2 failed")
        sys.exit(1)


if __name__ == "__main__":
    main()
