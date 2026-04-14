#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Summarize a SWE-bench runner output dir (runs/<run_id>/): patch_apply pass rate,
# empty_patch_reason histogram, engine_error samples, first AgentErrorEvent per sample.

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path
from typing import Any

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

from bench.swebench.util import sanitize_instance_id  # noqa: E402
from experiments.run_evidence import load_patch_apply_check, load_summary  # noqa: E402


def _first_agent_error(trace_path: Path) -> dict[str, Any] | None:
    if not trace_path.exists():
        return None
    try:
        data = json.loads(trace_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError):
        return None
    events = data.get("raw_events") or []
    for ev in events:
        if isinstance(ev, dict) and ev.get("kind") == "AgentErrorEvent":
            return ev
    return None


def main() -> int:
    p = argparse.ArgumentParser(description="Health snapshot for one runs/<run_id>/ directory.")
    p.add_argument("--run-dir", type=str, required=True, help="Path to runs/.../<run_id>/")
    p.add_argument("--json", action="store_true", help="Print machine-readable JSON only")
    p.add_argument("--sample", type=int, default=5, help="Max instances to show detail for")
    args = p.parse_args()
    run_dir = Path(args.run_dir).resolve()
    if not run_dir.is_dir():
        print("Error: run-dir is not a directory: %s" % run_dir, file=sys.stderr)
        return 2

    summary = load_summary(run_dir)
    instances = (summary or {}).get("instances") or []
    if not instances:
        print("Warning: no summary.json or empty instances list in %s" % run_dir, file=sys.stderr)

    applies_true = applies_false = 0
    stderr_buckets: Counter[str] = Counter()
    reason_buckets: Counter[str] = Counter()
    engine_errors: list[tuple[str, str]] = []
    samples: list[dict[str, Any]] = []

    for rec in instances:
        iid = rec.get("instance_id")
        if not iid:
            continue
        sid = sanitize_instance_id(str(iid))
        pac = load_patch_apply_check(run_dir, str(iid))
        if pac is None:
            continue
        if pac.get("applies") is True:
            applies_true += 1
        else:
            applies_false += 1
            stderr = (pac.get("stderr") or "").strip() or "(no stderr)"
            stderr_buckets[stderr[:120]] += 1
        r = pac.get("empty_patch_reason")
        if r:
            reason_buckets[str(r)] += 1

        meta_path = run_dir / sid / "metadata.json"
        err_line = ""
        if meta_path.exists():
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
                err_line = str(meta.get("engine_error") or "")[:200]
            except (json.JSONDecodeError, OSError):
                pass
        if err_line and len(engine_errors) < 20:
            engine_errors.append((str(iid), err_line))

        if len(samples) < max(0, args.sample):
            trace_path = run_dir / sid / "engine_trace.json"
            samples.append(
                {
                    "instance_id": str(iid),
                    "applies": pac.get("applies"),
                    "empty_patch_reason": pac.get("empty_patch_reason"),
                    "stderr_head": (pac.get("stderr") or "")[:160],
                    "engine_error_head": err_line,
                    "first_AgentErrorEvent": _first_agent_error(trace_path),
                }
            )

    total = applies_true + applies_false
    out: dict[str, Any] = {
        "run_dir": str(run_dir),
        "instances_in_summary": len(instances),
        "patch_apply": {
            "total": total,
            "applies_true": applies_true,
            "applies_false": applies_false,
            "pass_rate": round(applies_true / total, 4) if total else None,
        },
        "patch_apply_stderr_topN": [{"stderr": k, "count": v} for k, v in stderr_buckets.most_common(10)],
        "empty_patch_reason_topN": [{"reason": k, "count": v} for k, v in reason_buckets.most_common(10)],
        "engine_error_samples": [{"instance_id": a, "engine_error": b} for a, b in engine_errors[: args.sample]],
        "detail_samples": samples,
    }

    if args.json:
        print(json.dumps(out, indent=2))
        return 0

    print("run_dir: %s" % run_dir)
    print("patch_apply: %s applies_true / %s total (false=%s)" % (applies_true, total, applies_false))
    if stderr_buckets:
        print("apply stderr buckets (top 5):")
        for k, v in stderr_buckets.most_common(5):
            print("  %s x %s" % (v, k))
    if reason_buckets:
        print("empty_patch_reason:")
        for k, v in reason_buckets.most_common(10):
            print("  %s x %s" % (v, k))
    if engine_errors:
        print("engine_error samples:")
        for iid, msg in engine_errors[: args.sample]:
            print("  %s: %s" % (iid, msg[:120]))
    for s in samples:
        print("--- %s ---" % s["instance_id"])
        print("  applies=%s reason=%s" % (s.get("applies"), s.get("empty_patch_reason")))
        ae = s.get("first_AgentErrorEvent")
        if ae:
            print("  AgentErrorEvent: %s" % json.dumps(ae, indent=None)[:300])
    return 0


if __name__ == "__main__":
    sys.exit(main())
