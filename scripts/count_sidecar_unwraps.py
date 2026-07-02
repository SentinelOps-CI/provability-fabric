#!/usr/bin/env python3
"""Count .unwrap() / .expect() in sidecar-watcher production sources (F16 gate)."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "runtime" / "sidecar-watcher" / "src"
BASELINE = 10  # F16 target ceiling (2026-07-02 phase 2)

PATTERN = re.compile(r"\.(unwrap|expect)\(")


def is_test_context(lines: list[str], line_idx: int) -> bool:
    for i in range(line_idx, -1, -1):
        line = lines[i]
        if "#[cfg(test)]" in line:
            return True
        if line.strip().startswith("mod tests"):
            return True
        if line.strip() == "#[cfg(test)]":
            return True
        if i < line_idx and line.startswith("fn ") and "test" not in line:
            break
    return False


def count_unwraps() -> tuple[int, list[str]]:
    total = 0
    hits: list[str] = []
    for path in sorted(SRC.rglob("*.rs")):
        text = path.read_text(encoding="utf-8")
        lines = text.splitlines()
        in_tests = False
        for idx, line in enumerate(lines):
            if "#[cfg(test)]" in line:
                in_tests = True
            if line.strip() == "}" and in_tests and "mod tests" in "\n".join(lines[max(0, idx - 5) : idx]):
                in_tests = False
            if in_tests or "mod tests" in line:
                continue
            if PATTERN.search(line) and not line.strip().startswith("//"):
                total += len(PATTERN.findall(line))
                hits.append(f"{path.relative_to(ROOT)}:{idx + 1}: {line.strip()}")
    return total, hits


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--baseline",
        "--max",
        type=int,
        default=BASELINE,
        dest="baseline",
        help=f"Maximum allowed production unwrap/expect count (default {BASELINE})",
    )
    parser.add_argument("--list", action="store_true", help="Print each match")
    args = parser.parse_args()

    count, hits = count_unwraps()
    if args.list:
        for h in hits:
            print(h)
    print(f"sidecar production unwrap/expect count: {count} (baseline <= {args.baseline})")
    if count > args.baseline:
        print(
            f"ERROR: count {count} exceeds baseline {args.baseline}",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
