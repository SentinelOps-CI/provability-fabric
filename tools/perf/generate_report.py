#!/usr/bin/env python3
"""Summarize k6 JSON export for platform performance smoke workflows."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate performance report from k6 export")
    parser.add_argument("k6_results", type=Path, help="k6 --summary-export JSON file")
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=Path("performance-report.json"),
        help="Output report path",
    )
    args = parser.parse_args()

    if not args.k6_results.is_file():
        print(f"Missing k6 results: {args.k6_results}", file=sys.stderr)
        return 1

    data = json.loads(args.k6_results.read_text(encoding="utf-8"))
    metrics = data.get("metrics", {})
    report = {
        "source": str(args.k6_results),
        "http_req_duration_p95": metrics.get("http_req_duration", {})
        .get("values", {})
        .get("p(95)"),
        "http_req_failed_rate": metrics.get("http_req_failed", {})
        .get("values", {})
        .get("rate"),
        "iterations": metrics.get("iterations", {}).get("values", {}).get("count"),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
