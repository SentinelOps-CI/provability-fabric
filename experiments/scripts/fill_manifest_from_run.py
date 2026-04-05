#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Fill experiment manifest with pf_commit (and optionally agent_commit from env)
# and copy it alongside results so the run is tied to exact config.

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


def get_git_sha(repo_root: Path) -> str:
    try:
        out = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            timeout=5,
        )
        if out.returncode == 0 and out.stdout:
            return out.stdout.strip()[:40]
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    return ""


def main() -> int:
    if len(sys.argv) < 2:
        print("Usage: fill_manifest_from_run.py <manifest.json> [run_dir]", file=sys.stderr)
        print("  Fills pf_commit in manifest; optionally copies to run_dir.", file=sys.stderr)
        return 1
    manifest_path = Path(sys.argv[1]).resolve()
    run_dir = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else None
    repo_root = Path(__file__).resolve().parent.parent.parent  # experiments/scripts -> experiments -> repo
    if not manifest_path.exists():
        print(f"Manifest not found: {manifest_path}", file=sys.stderr)
        return 1
    data = json.loads(manifest_path.read_text(encoding="utf-8"))
    data["pf_commit"] = get_git_sha(repo_root)
    if not data.get("created_at"):
        from datetime import datetime, timezone
        data["created_at"] = datetime.now(timezone.utc).isoformat()
    agent_commit = os.environ.get("OPENHANDS_COMMIT") or os.environ.get("AGENT_COMMIT")
    if agent_commit and "agent_commit" in data:
        data["agent_commit"] = agent_commit
    manifest_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    if run_dir and run_dir.is_dir():
        dest = run_dir / "experiment_manifest.json"
        dest.write_text(json.dumps(data, indent=2), encoding="utf-8")
        print(f"Wrote {dest}")
    print(f"Filled pf_commit={data['pf_commit']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
