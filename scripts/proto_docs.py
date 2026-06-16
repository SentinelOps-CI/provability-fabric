#!/usr/bin/env python3
"""Generate a minimal API reference from api/v1 protobuf sources."""

from __future__ import annotations

import re
from datetime import datetime, timezone
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
PROTO_DIR = REPO_ROOT / "api" / "v1"
OUT = REPO_ROOT / "docs" / "api" / "api.md"

MESSAGE_RE = re.compile(r"^message\s+(\w+)")
SERVICE_RE = re.compile(r"^service\s+(\w+)")
ENUM_RE = re.compile(r"^enum\s+(\w+)")


def summarize(proto_path: Path) -> str:
    messages: list[str] = []
    services: list[str] = []
    enums: list[str] = []
    for line in proto_path.read_text(encoding="utf-8").splitlines():
        if match := MESSAGE_RE.match(line):
            messages.append(match.group(1))
        elif match := SERVICE_RE.match(line):
            services.append(match.group(1))
        elif match := ENUM_RE.match(line):
            enums.append(match.group(1))

    parts = [f"### `{proto_path.name}`", ""]
    if services:
        parts.append(f"- Services: {', '.join(services)}")
    if messages:
        parts.append(f"- Messages: {', '.join(messages)}")
    if enums:
        parts.append(f"- Enums: {', '.join(enums)}")
    parts.append("")
    return "\n".join(parts)


def main() -> None:
    protos = sorted(PROTO_DIR.glob("*.proto"))
    OUT.parent.mkdir(parents=True, exist_ok=True)
    generated = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    lines = [
        "# Provability Fabric API v1",
        "",
        f"Generated: {generated}",
        "",
        "Protobuf sources live under `api/v1/`. Lint with `buf lint` (see `api/buf.yaml`).",
        "",
    ]
    for proto in protos:
        lines.append(summarize(proto))
    OUT.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {OUT.relative_to(REPO_ROOT)}")


if __name__ == "__main__":
    main()
