# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# CLI entry point: pf bench swebench replay --run_id <id>

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .replay import ReplayResult, replay_run


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Replay SWE-bench run: replay tool trace, reconstitute patch, verify hash match.",
    )
    parser.add_argument(
        "--run-id",
        required=True,
        help="Run ID (directory under runs-dir)",
    )
    parser.add_argument(
        "--instance-id",
        default="",
        help="Optional: replay only this instance (sanitized dir name)",
    )
    parser.add_argument(
        "--instance-ids",
        default="",
        help="Optional: comma-separated instance IDs to replay (e.g. id1,id2,id3)",
    )
    parser.add_argument(
        "--runs-dir",
        default="runs",
        help="Base directory for runs (default: runs)",
    )
    parser.add_argument(
        "--workspaces-dir",
        default="",
        help="Optional: workspaces base for resolving repo path",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output results as JSON",
    )
    args = parser.parse_args()

    runs_dir = Path(args.runs_dir)
    run_dir = runs_dir / args.run_id
    workspaces_dir = Path(args.workspaces_dir) if args.workspaces_dir else None
    if args.instance_ids.strip():
        instance_filter = [s.strip() for s in args.instance_ids.split(",") if s.strip()]
    else:
        instance_filter = args.instance_id.strip() or None

    if not run_dir.is_dir():
        print(f"Run directory not found: {run_dir}", file=sys.stderr)
        return 1

    results, all_matched = replay_run(
        run_dir,
        instance_id_filter=instance_filter,
        workspaces_dir=workspaces_dir,
    )

    if args.json:
        out = {
            "run_id": args.run_id,
            "all_matched": all_matched,
            "replay_ok": bool(results) and all(r.success and r.match for r in results),
            "results": [
                {
                    "instance_id": r.instance_id,
                    "success": r.success,
                    "match": r.match,
                    "replay_ok": r.success and r.match,
                    "original_patch_sha256": r.original_patch_sha256,
                    "reconstituted_patch_sha256": r.reconstituted_patch_sha256,
                    "message": r.message,
                }
                for r in results
            ],
        }
        print(json.dumps(out, indent=2))
    else:
        for r in results:
            status = "MATCH" if r.match else "MISMATCH"
            print(f"{r.instance_id}: {status} - {r.message}")
        if not results:
            print("No instances replayed.", file=sys.stderr)
        elif all_matched:
            print("All replayed patches match original hash.")
        else:
            print("Some replayed patches did not match.", file=sys.stderr)

    return 0 if all_matched and results else 1


if __name__ == "__main__":
    sys.exit(main())
