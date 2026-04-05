#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
#
# After a golden cycle, optionally require non-zero harness solve rates (product readiness).

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Read compare.json solve rates; optionally fail if both are zero.",
    )
    ap.add_argument("--compare-json", required=True, type=Path)
    ap.add_argument(
        "--require-nonzero",
        action="store_true",
        help="Exit 1 if baseline or pf solve_rate is null or 0 (use after fixes + full re-run).",
    )
    args = ap.parse_args()
    p = args.compare_json
    if not p.exists():
        print("compare.json not found: %s" % p, file=sys.stderr)
        return 1
    try:
        c = json.loads(p.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print("invalid compare.json: %s" % e, file=sys.stderr)
        return 1
    b = (c.get("baseline") or {}).get("solve_rate")
    pf = (c.get("pf") or {}).get("solve_rate")
    print("baseline.solve_rate=%r pf.solve_rate=%r" % (b, pf))
    if args.require_nonzero:
        for name, v in (("baseline", b), ("pf", pf)):
            if v is None or (isinstance(v, (int, float)) and float(v) <= 0.0):
                print(
                    "check_golden_solve_rates: %s solve_rate is not positive. "
                    "Re-run the pipeline after agent/policy fixes; see "
                    "experiments/exp-step2-lite-smoke/diagnosis-roadmap.md"
                    % name,
                    file=sys.stderr,
                )
                return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
