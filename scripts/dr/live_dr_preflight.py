#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Fail-closed preflight for live cross-region DR.

Validates that required AWS DR secrets/config are present before any live
mutation. Does not call AWS. Intended for workflow_dispatch mode=live.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

REQUIRED_ENV = (
    "AWS_ACCESS_KEY_ID",
    "AWS_SECRET_ACCESS_KEY",
    "DNS_ZONE_ID",
    "HEALTH_CHECK_ID",
)


def main() -> int:
    missing = [name for name in REQUIRED_ENV if not os.environ.get(name, "").strip()]
    report = {
        "mode": "live",
        "live_aws": True,
        "required": list(REQUIRED_ENV),
        "missing": missing,
        "primary_region": os.environ.get("PRIMARY_REGION", "us-west-2"),
        "secondary_region": os.environ.get("SECONDARY_REGION", "us-east-1"),
        "dns_record": os.environ.get("DNS_RECORD", "db.provability-fabric.org"),
    }
    out = Path(os.environ.get("DR_LIVE_PREFLIGHT_REPORT", "reports/dr/live-dr-preflight.json"))
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    if missing:
        print(
            f"error: live DR invoked without required config: {', '.join(missing)}",
            file=sys.stderr,
        )
        print("fail-closed: set secrets and re-dispatch mode=live", file=sys.stderr)
        return 1
    print("live_dr_preflight: PASS (secrets present; proceeding to live AWS jobs)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
