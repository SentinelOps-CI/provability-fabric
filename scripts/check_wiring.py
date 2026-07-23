#!/usr/bin/env python3
"""Assert local compose wiring matches code/docs port defaults (Wave E2).

Checks docker-compose.yml published ports and env against the canonical local
contract in docs/dev/local-workflows.md:

  sidecar / kernel :8006
  ledger           :4000

Exit 0 on success; print findings and exit 1 on mismatch.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMPOSE = ROOT / "docker-compose.yml"

# (label, path relative to ROOT, regex that must match)
CODE_DEFAULTS: list[tuple[str, str, str]] = [
    (
        "ledger MCP sidecar default",
        "runtime/ledger/src/mcp/mcp-proxy.ts",
        r"DEFAULT_SIDECAR_URL\s*=\s*'http://localhost:8006'",
    ),
    (
        "ledger production SIDECAR_URL fallback",
        "runtime/ledger/src/profiles/production.ts",
        r"SIDECAR_URL\s*\|\|\s*'http://localhost:8006'",
    ),
    (
        "sidecar LEDGER_URL default",
        "runtime/sidecar-watcher/src/main.rs",
        r'LEDGER_URL".*"http://localhost:4000"',
    ),
    (
        "tool-broker KERNEL_URL default",
        "runtime/tool-broker/src/main.rs",
        r'KERNEL_URL".*"http://localhost:8006"',
    ),
]

# (label, regex against compose file)
COMPOSE_EXPECTATIONS: list[tuple[str, str]] = [
    ("sidecar host port 8006", r'"8006:8006"'),
    ("ledger host port 4000", r'"4000:4000"'),
    ("ledger PROFILE=dev", r"PROFILE=dev"),
    ("ledger SIDECAR_URL → sidecar:8006", r"SIDECAR_URL=http://runtime-sidecar:8006"),
    ("sidecar LEDGER_URL → ledger:4000", r"LEDGER_URL=http://ledger:4000"),
    ("tool-broker KERNEL_URL → sidecar:8006", r"KERNEL_URL=http://runtime-sidecar:8006"),
    ("tool-broker warm restart", r"restart:\s*unless-stopped"),
]


def main() -> int:
    errors: list[str] = []

    if not COMPOSE.is_file():
        print(f"FAIL: missing {COMPOSE}", file=sys.stderr)
        return 1

    compose_text = COMPOSE.read_text(encoding="utf-8")
    for label, pattern in COMPOSE_EXPECTATIONS:
        if not re.search(pattern, compose_text):
            errors.append(f"compose: missing {label} (/{pattern}/)")

    # Dead redis deps on ledger/sidecar (should not reappear until a consumer exists)
    for svc in ("runtime-sidecar", "ledger"):
        m = re.search(
            rf"(?ms)^  {re.escape(svc)}:\n(.*?)(?=^  [a-z0-9-]+:|\Z)",
            compose_text,
        )
        if not m:
            errors.append(f"compose: could not locate service block for {svc}")
            continue
        block = m.group(1)
        if "REDIS_URL" in block:
            errors.append(f"compose: {svc} still sets REDIS_URL (unused)")
        if re.search(r"depends_on:[\s\S]*?\bredis:", block):
            errors.append(f"compose: {svc} still depends_on redis")

    for label, rel, pattern in CODE_DEFAULTS:
        path = ROOT / rel
        if not path.is_file():
            errors.append(f"missing file for {label}: {rel}")
            continue
        text = path.read_text(encoding="utf-8")
        if not re.search(pattern, text, re.DOTALL):
            errors.append(f"code: {label} not found in {rel} (/{pattern}/)")

    schema = ROOT / "schemas" / "pf-env.schema.json"
    if not schema.is_file():
        errors.append("missing schemas/pf-env.schema.json")

    if errors:
        print("check_wiring: FAILED", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 1

    print("check_wiring: OK (compose <-> code defaults for :8006 / :4000)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
