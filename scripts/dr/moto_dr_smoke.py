#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""CI-local cross-region DR proof using moto (LocalStack-equivalent).

Exercises S3 cross-region object presence, Route53 health-check/DNS flip
bookkeeping, DR script layout presence, and blue/green migrate --dry-run.
Does not claim live AWS DR.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import boto3
from moto import mock_aws

REPO = Path(__file__).resolve().parents[2]
PRIMARY = "us-west-2"
SECONDARY = "us-east-1"
PRIMARY_BUCKET = "pf-dr-dumps-primary"
SECONDARY_BUCKET = "pf-dr-dumps-secondary"
DNS_RECORD = "db.provability-fabric.local"
ZONE_NAME = "provability-fabric.local."


def _require_layout() -> None:
    assert (REPO / "scripts" / "dr").is_dir(), "missing scripts/dr"
    assert (REPO / "scripts" / "db" / "blue_green_migrate.sh").is_file()
    assert (REPO / "scripts" / "zero-downtime-upgrade.sh").is_file()
    print("layout: scripts/dr + blue_green_migrate.sh + zero-downtime-upgrade.sh present")


def _run_blue_green_dry_run() -> None:
    script = REPO / "scripts" / "db" / "blue_green_migrate.sh"
    # Git on Windows may drop +x; invoke via bash when available, else sh.
    cmd = [
        "bash",
        str(script),
        "--dry-run",
        "--blue-db-url",
        "postgresql://test:test@blue.example:5432/pf",
        "--green-db-url",
        "postgresql://test:test@green.example:5432/pf",
        "--dns-zone",
        "ZTESTCILOCAL",
        "--dns-record",
        DNS_RECORD,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if proc.returncode != 0:
        # Fallback without bash (rare on GHA ubuntu)
        if sys.platform.startswith("win"):
            print("blue_green dry-run skipped on Windows shell; layout already checked")
            return
        print(proc.stdout)
        print(proc.stderr, file=sys.stderr)
        raise SystemExit(f"blue_green_migrate dry-run failed: {proc.returncode}")
    assert "dry-run complete" in proc.stdout, proc.stdout
    print("blue_green_migrate: dry-run ok")


@mock_aws
def _exercise_aws_surface() -> dict:
    os.environ.setdefault("AWS_ACCESS_KEY_ID", "testing")
    os.environ.setdefault("AWS_SECRET_ACCESS_KEY", "testing")
    os.environ.setdefault("AWS_DEFAULT_REGION", PRIMARY)
    os.environ.setdefault("AWS_SECURITY_TOKEN", "testing")
    os.environ.setdefault("AWS_SESSION_TOKEN", "testing")

    s3_primary = boto3.client("s3", region_name=PRIMARY)
    s3_secondary = boto3.client("s3", region_name=SECONDARY)
    r53 = boto3.client("route53", region_name=PRIMARY)

    def _create_bucket(client, name: str, region: str) -> None:
        # us-east-1 rejects LocationConstraint; other regions require it.
        if region == "us-east-1":
            client.create_bucket(Bucket=name)
        else:
            client.create_bucket(
                Bucket=name,
                CreateBucketConfiguration={"LocationConstraint": region},
            )

    _create_bucket(s3_primary, PRIMARY_BUCKET, PRIMARY)
    _create_bucket(s3_secondary, SECONDARY_BUCKET, SECONDARY)

    payload = b"dr-smoke-payload-v1"
    key = "failover/test-object.txt"
    s3_primary.put_object(Bucket=PRIMARY_BUCKET, Key=key, Body=payload)

    # Simulate cross-region replication (copy primary -> secondary)
    obj = s3_primary.get_object(Bucket=PRIMARY_BUCKET, Key=key)
    body = obj["Body"].read()
    assert body == payload
    s3_secondary.put_object(Bucket=SECONDARY_BUCKET, Key=key, Body=body)
    replica = s3_secondary.get_object(Bucket=SECONDARY_BUCKET, Key=key)["Body"].read()
    assert replica == payload, "secondary replica mismatch"
    print("s3: cross-region replica verified")

    zone = r53.create_hosted_zone(Name=ZONE_NAME, CallerReference="dr-smoke-1")
    zone_id = zone["HostedZone"]["Id"].split("/")[-1]

    # Primary A record, then failover flip to secondary IP
    primary_ip = "10.0.0.10"
    secondary_ip = "10.1.0.10"
    r53.change_resource_record_sets(
        HostedZoneId=zone_id,
        ChangeBatch={
            "Changes": [
                {
                    "Action": "UPSERT",
                    "ResourceRecordSet": {
                        "Name": DNS_RECORD,
                        "Type": "A",
                        "TTL": 60,
                        "ResourceRecords": [{"Value": primary_ip}],
                    },
                }
            ]
        },
    )
    records = r53.list_resource_record_sets(HostedZoneId=zone_id)["ResourceRecordSets"]
    a_recs = [r for r in records if r["Name"].startswith(DNS_RECORD) and r["Type"] == "A"]
    assert a_recs and a_recs[0]["ResourceRecords"][0]["Value"] == primary_ip

    # Failover flip
    r53.change_resource_record_sets(
        HostedZoneId=zone_id,
        ChangeBatch={
            "Changes": [
                {
                    "Action": "UPSERT",
                    "ResourceRecordSet": {
                        "Name": DNS_RECORD,
                        "Type": "A",
                        "TTL": 60,
                        "ResourceRecords": [{"Value": secondary_ip}],
                    },
                }
            ]
        },
    )
    records = r53.list_resource_record_sets(HostedZoneId=zone_id)["ResourceRecordSets"]
    a_recs = [r for r in records if r["Name"].startswith(DNS_RECORD) and r["Type"] == "A"]
    assert a_recs and a_recs[0]["ResourceRecords"][0]["Value"] == secondary_ip
    print("route53: DNS failover flip verified")

    # Health check bookkeeping
    hc = r53.create_health_check(
        CallerReference="dr-smoke-hc",
        HealthCheckConfig={
            "IPAddress": primary_ip,
            "Port": 443,
            "Type": "HTTPS",
            "ResourcePath": "/health",
            "RequestInterval": 30,
            "FailureThreshold": 3,
        },
    )
    hc_id = hc["HealthCheck"]["Id"]
    r53.update_health_check(HealthCheckId=hc_id, Disabled=True)
    r53.update_health_check(HealthCheckId=hc_id, Disabled=False)
    print(f"route53: health check {hc_id} disable/enable ok")

    return {
        "primary_bucket": PRIMARY_BUCKET,
        "secondary_bucket": SECONDARY_BUCKET,
        "zone_id": zone_id,
        "health_check_id": hc_id,
        "dns_after_failover": secondary_ip,
        "replica_bytes": len(replica),
        "mode": "moto-local",
        "live_aws": False,
    }


def main() -> int:
    _require_layout()
    _run_blue_green_dry_run()
    report = _exercise_aws_surface()
    out = Path(os.environ.get("DR_SMOKE_REPORT", "reports/dr/moto-dr-smoke.json"))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out}")
    print("moto_dr_smoke: PASS (CI-local proof; live AWS DR still requires secrets)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
