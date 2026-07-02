#!/usr/bin/env python3
"""Count explicit `any` usages in runtime/ledger/src (F27 gate)."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "runtime" / "ledger" / "src"
BASELINE = 152
CEILING = 20

PATTERN = re.compile(r"\bany\b")


def count_any() -> tuple[int, int]:
    total = 0
    non_test = 0
    for path in sorted(SRC.rglob("*")):
        if path.suffix not in {".ts", ".tsx", ".js", ".cjs"}:
            continue
        if "__tests__" in path.parts or path.name.endswith(".test.ts"):
            continue
        text = path.read_text(encoding="utf-8")
        matches = len(PATTERN.findall(text))
        total += matches
        non_test += matches
    return total, non_test


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ceiling",
        "--max",
        type=int,
        default=CEILING,
        dest="ceiling",
        help=f"Target ceiling for non-test `any` (default {CEILING}); --max is an alias",
    )
    parser.add_argument(
        "--baseline",
        type=int,
        default=BASELINE,
        help=f"Hard baseline — fail if count increases above this (default {BASELINE})",
    )
    args = parser.parse_args()

    total, non_test = count_any()
    print(f"ledger src `any` count (excl. tests): {non_test}")
    print(f"ledger src `any` count (all): {total}")
    print(f"target ceiling: {args.ceiling}; regression baseline: {args.baseline}")

    if non_test > args.baseline:
        print(
            f"ERROR: count {non_test} exceeds regression baseline {args.baseline}",
            file=sys.stderr,
        )
        return 1
    if non_test > args.ceiling:
        print(
            f"ERROR: count {non_test} exceeds target ceiling {args.ceiling}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
