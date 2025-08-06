#!/usr/bin/env python3
"""
SPDX-License-Identifier: Apache-2.0
Copyright 2025 Provability-Fabric Contributors

Retention Probe - Validates zero-retention compliance.
Queries storage systems for content older than TTL limits and alerts on violations.
"""

import asyncio
import json
import logging
import sys
import time
from datetime import datetime, timedelta
from typing import Dict, List, Optional

import aioredis
import asyncpg
import argparse
from dataclasses import dataclass


@dataclass
class ProbeConfig:
    """Configuration for retention probe."""

    redis_url: str = "redis://localhost:6379"
    postgres_url: str = (
        "postgresql://pf_user:pf_password@localhost:5432/provability_fabric"
    )
    max_raw_content_ttl: int = 600  # 10 minutes in seconds
    probe_interval: int = 60  # 1 minute
    alert_threshold: int = 0  # Alert on any violations
    output_file: Optional[str] = None


@dataclass
class ProbeResult:
    """Result of a retention probe."""

    timestamp: datetime
    total_violations: int
    redis_violations: List[str]
    postgres_violations: List[str]
    compliance_status: bool
    details: Dict


class RetentionProbe:
    def __init__(self, config: ProbeConfig):
        self.config = config
        self.logger = logging.getLogger(__name__)

    async def run_probe(self) -> ProbeResult:
        """Run a complete retention probe."""
        self.logger.info("Starting retention probe...")

        redis_violations = await self._check_redis_retention()
        postgres_violations = await self._check_postgres_retention()

        total_violations = len(redis_violations) + len(postgres_violations)
        compliance_status = total_violations <= self.config.alert_threshold

        result = ProbeResult(
            timestamp=datetime.utcnow(),
            total_violations=total_violations,
            redis_violations=redis_violations,
            postgres_violations=postgres_violations,
            compliance_status=compliance_status,
            details={
                "max_ttl_seconds": self.config.max_raw_content_ttl,
                "probe_interval": self.config.probe_interval,
                "redis_url": self.config.redis_url.split("@")[-1],  # Hide credentials
                "postgres_url": self.config.postgres_url.split("@")[
                    -1
                ],  # Hide credentials
            },
        )

        await self._report_result(result)
        return result

    async def _check_redis_retention(self) -> List[str]:
        """Check Redis for TTL violations."""
        violations = []

        try:
            redis = aioredis.from_url(self.config.redis_url)

            # Check raw query keys
            raw_query_keys = await redis.keys("query:raw:*")
            for key in raw_query_keys:
                ttl = await redis.ttl(key)
                if ttl == -1:  # No expiration set
                    violations.append(
                        f"Redis key {key.decode()} has no TTL (should expire)"
                    )
                elif ttl > self.config.max_raw_content_ttl:
                    violations.append(
                        f"Redis key {key.decode()} TTL {ttl}s exceeds max {self.config.max_raw_content_ttl}s"
                    )

            # Check raw result keys
            raw_result_keys = await redis.keys("result:raw:*")
            for key in raw_result_keys:
                ttl = await redis.ttl(key)
                if ttl == -1:  # No expiration set
                    violations.append(
                        f"Redis key {key.decode()} has no TTL (should expire)"
                    )
                elif ttl > self.config.max_raw_content_ttl:
                    violations.append(
                        f"Redis key {key.decode()} TTL {ttl}s exceeds max {self.config.max_raw_content_ttl}s"
                    )

            # Check for any content older than max TTL by checking creation time
            # (This requires timestamp tracking in keys or separate metadata)
            heartbeat_keys = await redis.keys("heartbeat:*")
            current_time = time.time()

            for key in heartbeat_keys:
                heartbeat_data = await redis.get(key)
                if heartbeat_data:
                    try:
                        data = json.loads(heartbeat_data)
                        timestamp = data.get("timestamp", 0)
                        age = current_time - timestamp

                        if age > self.config.max_raw_content_ttl:
                            violations.append(
                                f"Heartbeat {key.decode()} age {age:.0f}s exceeds max TTL"
                            )
                    except json.JSONDecodeError:
                        continue

            await redis.close()

        except Exception as e:
            self.logger.error(f"Failed to check Redis retention: {e}")
            violations.append(f"Redis probe failed: {str(e)}")

        return violations

    async def _check_postgres_retention(self) -> List[str]:
        """Check PostgreSQL for retention violations."""
        violations = []

        try:
            conn = await asyncpg.connect(self.config.postgres_url)

            # Check for raw content that should have been deleted
            # Look for records with raw content older than TTL
            cutoff_time = datetime.utcnow() - timedelta(
                seconds=self.config.max_raw_content_ttl
            )

            # Check capsules table for any raw content (if stored)
            query = """
            SELECT id, created_at, 
                   EXTRACT(EPOCH FROM (NOW() - created_at)) as age_seconds
            FROM "Capsule" 
            WHERE created_at < $1 
            AND (spec_sig LIKE '%raw%' OR reason LIKE '%raw%')
            """

            old_records = await conn.fetch(query, cutoff_time)
            for record in old_records:
                violations.append(
                    f"Capsule {record['id']} contains potential raw content, "
                    f"age {record['age_seconds']:.0f}s exceeds max TTL"
                )

            # Check for usage events with raw content
            usage_query = """
            SELECT id, created_at,
                   EXTRACT(EPOCH FROM (NOW() - created_at)) as age_seconds
            FROM "UsageEvent" 
            WHERE created_at < $1 
            AND (event_data::text LIKE '%raw%' OR event_data::text LIKE '%content%')
            """

            try:
                old_usage = await conn.fetch(usage_query, cutoff_time)
                for record in old_usage:
                    violations.append(
                        f"UsageEvent {record['id']} may contain raw content, "
                        f"age {record['age_seconds']:.0f}s exceeds max TTL"
                    )
            except Exception:
                # Table might not exist, skip
                pass

            await conn.close()

        except Exception as e:
            self.logger.error(f"Failed to check PostgreSQL retention: {e}")
            violations.append(f"PostgreSQL probe failed: {str(e)}")

        return violations

    async def _report_result(self, result: ProbeResult):
        """Report probe results."""
        if result.compliance_status:
            self.logger.info(
                f"✅ Retention probe PASSED: {result.total_violations} violations"
            )
        else:
            self.logger.error(
                f"❌ Retention probe FAILED: {result.total_violations} violations"
            )

        # Log details
        for violation in result.redis_violations:
            self.logger.warning(f"Redis violation: {violation}")

        for violation in result.postgres_violations:
            self.logger.warning(f"PostgreSQL violation: {violation}")

        # Write to output file if specified
        if self.config.output_file:
            report = {
                "timestamp": result.timestamp.isoformat(),
                "compliance_status": result.compliance_status,
                "total_violations": result.total_violations,
                "redis_violations": result.redis_violations,
                "postgres_violations": result.postgres_violations,
                "details": result.details,
            }

            with open(self.config.output_file, "w") as f:
                json.dump(report, f, indent=2)

            self.logger.info(f"Probe report written to {self.config.output_file}")

    async def run_continuous(self):
        """Run probe continuously at specified interval."""
        self.logger.info(
            f"Starting continuous retention probe (interval: {self.config.probe_interval}s)"
        )

        while True:
            try:
                result = await self.run_probe()

                if not result.compliance_status:
                    self.logger.critical("RETENTION COMPLIANCE VIOLATION DETECTED!")
                    # In production, this would trigger alerts

                await asyncio.sleep(self.config.probe_interval)

            except KeyboardInterrupt:
                self.logger.info("Probe stopped by user")
                break
            except Exception as e:
                self.logger.error(f"Probe error: {e}")
                await asyncio.sleep(self.config.probe_interval)


async def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Retention compliance probe")
    parser.add_argument(
        "--redis-url", default="redis://localhost:6379", help="Redis connection URL"
    )
    parser.add_argument(
        "--postgres-url",
        default="postgresql://pf_user:pf_password@localhost:5432/provability_fabric",
        help="PostgreSQL connection URL",
    )
    parser.add_argument(
        "--max-ttl",
        type=int,
        default=600,
        help="Maximum TTL for raw content in seconds",
    )
    parser.add_argument(
        "--interval", type=int, default=60, help="Probe interval in seconds"
    )
    parser.add_argument("--output", help="Output file for probe results")
    parser.add_argument("--once", action="store_true", help="Run probe once and exit")
    parser.add_argument("--verbose", action="store_true", help="Enable verbose logging")

    args = parser.parse_args()

    # Configure logging
    level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=level, format="%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    )

    config = ProbeConfig(
        redis_url=args.redis_url,
        postgres_url=args.postgres_url,
        max_raw_content_ttl=args.max_ttl,
        probe_interval=args.interval,
        output_file=args.output,
    )

    probe = RetentionProbe(config)

    if args.once:
        result = await probe.run_probe()
        sys.exit(0 if result.compliance_status else 1)
    else:
        await probe.run_continuous()


if __name__ == "__main__":
    asyncio.run(main())
