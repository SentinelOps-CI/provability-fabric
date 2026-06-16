#!/usr/bin/env python3
"""Report certificate compliance rate for platform CERT validation workflows."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def _count_json_files(root: Path) -> tuple[int, int]:
    total = 0
    valid = 0
    if not root.exists():
        return total, valid
    for path in root.rglob("*.json"):
        total += 1
        try:
            json.loads(path.read_text(encoding="utf-8"))
            valid += 1
        except (json.JSONDecodeError, OSError):
            pass
    return total, valid


def main() -> int:
    parser = argparse.ArgumentParser(description="Check CERT JSON compliance rate")
    parser.add_argument(
        "--threshold",
        type=float,
        default=0.999,
        help="Minimum valid/total ratio (default: 0.999)",
    )
    args = parser.parse_args()

    roots = [Path("evidence/egress_certs"), Path("evidence/certs"), Path("tests/replay/out/certs")]
    total = 0
    valid = 0
    for root in roots:
        t, v = _count_json_files(root)
        total += t
        valid += v

    rate = 1.0 if total == 0 else valid / total
    report = {
        "compliance_rate": rate,
        "valid_certificates": valid,
        "total_certificates": total,
        "threshold": args.threshold,
    }

    for name in ("compliance-report.json", "cert-validation-report.json"):
        Path(name).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print(json.dumps(report, indent=2))
    if rate < args.threshold:
        print(
            f"Compliance rate {rate:.4f} below threshold {args.threshold}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
