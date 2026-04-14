#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Append one row to the Scale Results Ledger (JSONL) from compare.json and optional stress_summary.
# Invoke after a green run or after any experiment run to keep results cumulative.

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_SCHEMA_DIR = _SCRIPT_DIR.parent / "schemas"


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Append one experiment row to the Scale Results Ledger (JSONL).",
    )
    ap.add_argument("--compare-json", type=Path, required=True, help="Path to compare.json")
    ap.add_argument("--experiment-id", required=True, help="Experiment ID (e.g. exp-step2-lite-smoke)")
    ap.add_argument("--ledger", type=Path, default=None, help="Ledger file (default: experiments/scale-results-ledger.jsonl)")
    ap.add_argument("--stress-summary", type=Path, default=None, help="Optional stress_summary.json for timeout rates and guard_overhead")
    ap.add_argument("--pf-commit", default="", help="PF repo commit (e.g. git rev-parse --short=12 HEAD)")
    ap.add_argument("--agent-commit", default="", help="Agent/image version (e.g. openhands_version from env)")
    args = ap.parse_args()

    compare_path = args.compare_json
    if not compare_path.exists():
        print("Error: compare.json not found: %s" % compare_path, file=sys.stderr)
        return 1

    try:
        compare = json.loads(compare_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        print("Error: failed to load compare.json: %s" % e, file=sys.stderr)
        return 1

    baseline = compare.get("baseline") or {}
    pf = compare.get("pf") or {}
    delta = compare.get("delta") or {}
    replay = compare.get("replay") or {}
    empty_top = compare.get("empty_patch_reasons_topN") or []
    env_drift = compare.get("env_drift")

    row = {
        "date": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "experiment_id": args.experiment_id,
        "pf_commit": args.pf_commit or None,
        "agent_commit": args.agent_commit or None,
        "baseline_solve_rate": baseline.get("solve_rate"),
        "pf_solve_rate": pf.get("solve_rate"),
        "delta_solve_rate": delta.get("solve_rate"),
        "timeout_rate_baseline": None,
        "timeout_rate_pf": None,
        "empty_patch_reasons_top5": [{"reason": r.get("reason"), "count": r.get("count")} for r in empty_top[:5]],
        "replay_sample_size": replay.get("sample_size"),
        "replay_success_rate": replay.get("success_rate"),
        "replay_mismatch_count": replay.get("mismatch_count"),
        "env_drift_summary": "present" if (env_drift and isinstance(env_drift, dict) and env_drift) else ("empty_or_absent"),
    }

    if args.stress_summary and args.stress_summary.exists():
        try:
            stress = json.loads(args.stress_summary.read_text(encoding="utf-8"))
            row["timeout_rate_baseline"] = stress.get("timeout_rate_baseline")
            row["timeout_rate_pf"] = stress.get("timeout_rate_pf")
            row["guard_overhead_s_median"] = stress.get("guard_overhead_s_median")
        except (json.JSONDecodeError, OSError):
            pass

    ledger_path = args.ledger
    if ledger_path is None:
        ledger_path = _SCRIPT_DIR.parent / "scale-results-ledger.jsonl"

    ledger_path = ledger_path.resolve()
    ledger_path.parent.mkdir(parents=True, exist_ok=True)

    # Validate row against schema (schema-driven format)
    schema_path = _SCHEMA_DIR / "scale_results_ledger_row.schema.json"
    if schema_path.exists():
        try:
            import jsonschema
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            jsonschema.validate(row, schema)
        except ImportError:
            pass
        except jsonschema.ValidationError as e:
            print("Error: ledger row schema validation failed: %s" % e, file=sys.stderr)
            return 1

    with open(ledger_path, "a", encoding="utf-8") as f:
        f.write(json.dumps(row, ensure_ascii=False) + "\n")

    print("Appended to %s" % ledger_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
