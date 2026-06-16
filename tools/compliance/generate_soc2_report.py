#!/usr/bin/env python3
"""Generate docs/compliance/soc2.md from an evidence manifest."""

from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path


def main() -> int:
    manifest_path = Path(sys.argv[1] if len(sys.argv) > 1 else "evidence-manifest.json")
    out_path = Path(sys.argv[2] if len(sys.argv) > 2 else "docs/compliance/soc2.md")

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    generated = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

    lines = [
        "# SOC 2 / ISO 42001 Compliance Report",
        "",
        f"Generated: {generated}",
        f"Repository: {manifest.get('repo', 'unknown')}",
        f"Run ID: {manifest.get('run_id', 'unknown')}",
        "",
        "## Control Coverage Summary",
        "",
    ]

    control_artifacts: dict[str, list[dict]] = {}
    for artifact in manifest.get("artifacts", []):
        control_artifacts.setdefault(artifact["control_id"], []).append(artifact)

    for control_id, artifacts in sorted(control_artifacts.items()):
        lines.append(f"### {control_id}")
        lines.append("")
        lines.append(f"**Artifacts:** {len(artifacts)}")
        lines.append("")
        for artifact in artifacts:
            name = artifact.get("artifact_name", "unknown")
            sha256 = artifact.get("sha256", "")
            link = artifact.get("link", "")
            collected = artifact.get("collected_at", "")
            lines.append(f"- **{name}**")
            lines.append(f"  - SHA256: `{sha256}`")
            lines.append(f"  - Link: {link}")
            lines.append(f"  - Collected: {collected}")
            lines.append("")

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"Generated compliance report: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
