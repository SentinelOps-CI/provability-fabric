#!/usr/bin/env python3
"""
Scan GitHub workflow files for false-green patterns:
  - continue-on-error: true
  - || true
  - passWithNoTests

Exit 1 when unlisted patterns are found (unless --warn-only).
Justified entries must include a comment: # ci-honesty: justified <issue-url-or-tracker-id>
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


JUSTIFY_RE = re.compile(r"ci-honesty:\s*justified", re.I)
PATTERNS: list[tuple[str, re.Pattern[str]]] = [
    ("continue-on-error: true", re.compile(r"continue-on-error:\s*true\b")),
    ("|| true", re.compile(r"\|\|\s*true\b")),
    ("passWithNoTests", re.compile(r"passWithNoTests")),
]


@dataclass
class Finding:
    file: Path
    line_no: int
    pattern: str
    text: str
    justified: bool


def scan_file(path: Path) -> list[Finding]:
    findings: list[Finding] = []
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    for idx, line in enumerate(lines, start=1):
        window = "\n".join(lines[max(0, idx - 3) : min(len(lines), idx + 1)])
        justified = bool(JUSTIFY_RE.search(window))
        for name, pattern in PATTERNS:
            if pattern.search(line):
                findings.append(
                    Finding(
                        file=path,
                        line_no=idx,
                        pattern=name,
                        text=line.strip(),
                        justified=justified,
                    )
                )
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit CI workflows for false-green patterns.")
    parser.add_argument(
        "--workflows-dir",
        default=".github/workflows",
        help="Directory containing workflow YAML files",
    )
    parser.add_argument(
        "--warn-only",
        action="store_true",
        help="Print report but always exit 0",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    wf_dir = root / args.workflows_dir
    if not wf_dir.is_dir():
        print(f"error: workflows dir not found: {wf_dir}", file=sys.stderr)
        return 2

    all_findings: list[Finding] = []
    for wf in sorted(wf_dir.glob("*.yml")) + sorted(wf_dir.glob("*.yaml")):
        all_findings.extend(scan_file(wf))

    unjustified = [f for f in all_findings if not f.justified]
    justified = [f for f in all_findings if f.justified]

    print("CI honesty audit report")
    print("=" * 60)
    print(f"Total matches: {len(all_findings)}")
    print(f"Justified (ci-honesty comment): {len(justified)}")
    print(f"Unjustified: {len(unjustified)}")
    print()

    by_pattern: dict[str, int] = {}
    for f in all_findings:
        by_pattern[f.pattern] = by_pattern.get(f.pattern, 0) + 1
    for pattern, count in sorted(by_pattern.items()):
        print(f"  {pattern}: {count}")

    if unjustified:
        print("\nUnjustified findings (fix or add '# ci-honesty: justified <ref>' nearby):")
        for f in unjustified:
            rel = f.file.relative_to(root)
            print(f"  {rel}:{f.line_no} [{f.pattern}] {f.text}")

    if args.warn_only:
        return 0
    return 1 if unjustified else 0


if __name__ == "__main__":
    raise SystemExit(main())
