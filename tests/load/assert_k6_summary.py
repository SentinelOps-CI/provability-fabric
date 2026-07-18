#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Fail CI if a k6 --summary-export JSON misses latency/error-rate gates."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path)
    parser.add_argument("--max-fail-rate", type=float, default=0.01)
    parser.add_argument("--max-p95-ms", type=float, default=500.0)
    parser.add_argument("--min-checks-rate", type=float, default=0.99)
    args = parser.parse_args()

    data = json.loads(args.summary.read_text(encoding="utf-8"))
    metrics = data.get("metrics") or {}

    failed = metrics.get("http_req_failed") or {}
    fail_rate = failed.get("value")
    if fail_rate is None and "rates" in failed:
        fail_rate = failed["rates"].get("rate")
    # k6 summary-export shapes vary by version
    if fail_rate is None:
        fail_rate = (failed.get("values") or {}).get("rate")
    if fail_rate is None:
        # Fallback: count fails/passes
        fails = (metrics.get("http_req_failed") or {}).get("fails", 0)
        passes = (metrics.get("http_req_failed") or {}).get("passes", 0)
        total = fails + passes
        fail_rate = (fails / total) if total else 0.0

    duration = metrics.get("http_req_duration") or {}
    p95 = None
    for key in ("p(95)", "p95"):
        if key in (duration.get("values") or {}):
            p95 = duration["values"][key]
            break
    if p95 is None:
        p95 = (duration.get("values") or {}).get("avg")

    checks = metrics.get("checks") or {}
    checks_rate = checks.get("value")
    if checks_rate is None:
        checks_rate = (checks.get("values") or {}).get("rate")
    if checks_rate is None:
        passes = checks.get("passes", 0)
        fails = checks.get("fails", 0)
        total = passes + fails
        checks_rate = (passes / total) if total else 1.0

    print(
        json.dumps(
            {
                "http_req_failed_rate": fail_rate,
                "http_req_duration_p95_ms": p95,
                "checks_rate": checks_rate,
            },
            indent=2,
        )
    )

    errors = []
    if fail_rate is None or fail_rate > args.max_fail_rate:
        errors.append(f"fail_rate {fail_rate} > {args.max_fail_rate}")
    if p95 is None or p95 > args.max_p95_ms:
        errors.append(f"p95 {p95} ms > {args.max_p95_ms}")
    if checks_rate is None or checks_rate < args.min_checks_rate:
        errors.append(f"checks_rate {checks_rate} < {args.min_checks_rate}")

    # Thresholds block from k6 itself
    thresholds = data.get("root_group", {}).get("checks")  # may be absent
    root_thresholds = data.get("thresholds") or {}
    for name, info in root_thresholds.items():
        if isinstance(info, dict) and info.get("ok") is False:
            errors.append(f"threshold failed: {name}")

    if errors:
        print("assert_k6_summary: FAIL", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print("assert_k6_summary: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
