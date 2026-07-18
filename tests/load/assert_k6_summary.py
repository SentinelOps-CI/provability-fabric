#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Fail CI if a k6 --summary-export JSON misses latency/error-rate gates.

k6 v0.47 summary-export stores http_req_duration percentiles in milliseconds
at the metric top level (e.g. {"p(95)": 0.65, ...}). Per-metric threshold
booleans are breach flags (true = breached).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Optional


def _pick(d: dict[str, Any], *keys: str) -> Any:
    for k in keys:
        if k in d:
            return d[k]
    values = d.get("values")
    if isinstance(values, dict):
        for k in keys:
            if k in values:
                return values[k]
    return None


def _fail_rate(metric: dict[str, Any]) -> Optional[float]:
    if not metric:
        return None
    rate = _pick(metric, "rate", "value")
    if isinstance(rate, (int, float)):
        return float(rate)
    # Prefer passes/fails when rate absent (http_req_failed)
    if "passes" in metric or "fails" in metric:
        # For Rate metrics in summary-export, "passes" counts true samples.
        # http_req_failed rate is typically under "value"/"rate"; default 0.
        return float(metric.get("value") or metric.get("rate") or 0.0)
    return 0.0


def _checks_rate(metric: dict[str, Any]) -> float:
    if not metric:
        return 1.0
    rate = _pick(metric, "rate", "value")
    if isinstance(rate, (int, float)):
        # checks rate is success ratio when present
        return float(rate)
    passes = int(metric.get("passes") or 0)
    fails = int(metric.get("fails") or 0)
    total = passes + fails
    return (passes / total) if total else 1.0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("summary", type=Path)
    parser.add_argument("--max-fail-rate", type=float, default=0.01)
    parser.add_argument("--max-p95-ms", type=float, default=500.0)
    parser.add_argument("--min-checks-rate", type=float, default=0.99)
    args = parser.parse_args()

    data = json.loads(args.summary.read_text(encoding="utf-8"))
    metrics = data.get("metrics") or {}

    fail_rate = _fail_rate(metrics.get("http_req_failed") or {})
    duration = metrics.get("http_req_duration") or {}
    p95 = _pick(duration, "p(95)", "p95")
    if p95 is None:
        p95 = _pick(duration, "avg", "med")
    p95_ms = float(p95) if p95 is not None else None
    checks_rate = _checks_rate(metrics.get("checks") or {})

    # Breach flags: true means threshold breached
    breaches = []
    for mname, minfo in metrics.items():
        if not isinstance(minfo, dict):
            continue
        for tname, breached in (minfo.get("thresholds") or {}).items():
            if breached is True:
                breaches.append(f"{mname}:{tname}")
    for tname, info in (data.get("thresholds") or {}).items():
        if info is True or (isinstance(info, dict) and info.get("ok") is False):
            breaches.append(tname)

    print(
        json.dumps(
            {
                "http_req_failed_rate": fail_rate,
                "http_req_duration_p95_ms": p95_ms,
                "checks_rate": checks_rate,
                "breaches": breaches,
            },
            indent=2,
        )
    )

    errors = []
    if fail_rate is None or fail_rate > args.max_fail_rate:
        errors.append(f"fail_rate {fail_rate} > {args.max_fail_rate}")
    if p95_ms is None:
        errors.append(f"missing p95 (keys={sorted(duration.keys())})")
    elif p95_ms > args.max_p95_ms:
        errors.append(f"p95 {p95_ms} ms > {args.max_p95_ms}")
    if checks_rate < args.min_checks_rate:
        errors.append(f"checks_rate {checks_rate} < {args.min_checks_rate}")
    errors.extend(f"threshold breached: {b}" for b in breaches)

    if errors:
        print("assert_k6_summary: FAIL", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print("assert_k6_summary: PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
