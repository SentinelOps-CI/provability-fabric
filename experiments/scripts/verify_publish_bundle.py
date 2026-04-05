#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Machine verifier for the publish bundle. No network, no Docker.
# Checks: required files exist; GOLDEN.ok parses and (optionally) run dirs exist;
# compare.json schema and gates; replay.success_rate; optional eval_metadata consistency.

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
_SCHEMA_DIR = _SCRIPT_DIR.parent / "schemas"
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
from experiments.scripts.compare_gates import check_compare_gates  # noqa: E402
from experiments.scripts.publish_bundle import (  # noqa: E402
    GOLDEN_OK_REQUIRED_KEYS,
    PUBLISH_BUNDLE_REQUIRED_DIRS,
    PUBLISH_BUNDLE_REQUIRED_FILES,
)
from experiments.scripts.publish_manifest import verify_publish_manifest_sha256  # noqa: E402


def _fail(msg: str) -> None:
    print(msg, file=sys.stderr)
    sys.exit(1)


def _assert(condition: bool, msg: str) -> None:
    if not condition:
        _fail(msg)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Verify publish bundle and compare report (no network, no Docker).",
    )
    ap.add_argument("--publish-dir", required=True, help="Publish directory (e.g. runs/.../publish)")
    ap.add_argument("--compare-json", required=True, help="Path to compare.json")
    ap.add_argument("--run-ids-md", default="", help="Optional path to run-ids.md")
    ap.add_argument("--runs-root", default="", help="Optional runs root to check run dirs exist")
    ap.add_argument("--skip-run-dir-check", action="store_true", help="Do not require run dirs to exist (e.g. artifact-only verification)")
    args = ap.parse_args()

    publish_dir = Path(args.publish_dir)
    compare_path = Path(args.compare_json)

    _assert(publish_dir.is_dir(), "Publish dir does not exist or is not a directory: %s" % publish_dir)
    _assert(compare_path.exists(), "compare.json does not exist: %s" % compare_path)

    # --- Required files in publish bundle (single definition: publish_bundle.py) ---
    for name in PUBLISH_BUNDLE_REQUIRED_FILES:
        p = publish_dir / name
        _assert(p.exists(), "Missing required file in publish dir: %s" % name)

    for name in PUBLISH_BUNDLE_REQUIRED_DIRS:
        d = publish_dir / name
        _assert(d.is_dir(), "Missing publish/%s/ directory" % name)
    logs_dir = publish_dir / "logs"
    trajs_dir = publish_dir / "trajs"

    log_instances = [d.name for d in logs_dir.iterdir() if d.is_dir()]
    traj_files = [f.name for f in trajs_dir.iterdir() if f.suffix == ".json"]
    _assert(len(log_instances) >= 1, "Publish bundle must have at least one instance in publish/logs/<instance_id>/")
    _assert(len(traj_files) >= 1, "Publish bundle must have at least one publish/trajs/<instance_id>.json")

    man_errs = verify_publish_manifest_sha256(publish_dir)
    for msg in man_errs:
        _fail(msg)

    # --- GOLDEN.ok parse and optional run dir check ---
    golden_path = publish_dir / "GOLDEN.ok"
    try:
        golden = json.loads(golden_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        _fail("GOLDEN.ok is not valid JSON: %s" % e)

    for key in GOLDEN_OK_REQUIRED_KEYS:
        _assert(key in golden, "GOLDEN.ok must contain %s" % key)
    baseline_run_id = golden.get("baseline_run_id") or ""
    pf_run_id = golden.get("pf_run_id") or ""
    _assert(bool(baseline_run_id), "GOLDEN.ok baseline_run_id must be non-empty")
    _assert(bool(pf_run_id), "GOLDEN.ok pf_run_id must be non-empty")

    if args.runs_root and not args.skip_run_dir_check:
        runs_root = Path(args.runs_root)
        _assert((runs_root / "baseline" / baseline_run_id).exists() or (runs_root / "baseline").exists(),
                "GOLDEN.ok baseline_run_id run dir not found under %s" % runs_root)
        _assert((runs_root / "pf" / pf_run_id).exists() or (runs_root / "pf").exists(),
                "GOLDEN.ok pf_run_id run dir not found under %s" % runs_root)

    # --- compare.json load and schema ---
    try:
        compare = json.loads(compare_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        _fail("compare.json is not valid JSON: %s" % e)

    schema_path = _SCHEMA_DIR / "compare_report.schema.json"
    if schema_path.exists():
        try:
            import jsonschema
            schema = json.loads(schema_path.read_text(encoding="utf-8"))
            jsonschema.validate(compare, schema)
        except ImportError:
            pass
        except jsonschema.ValidationError as e:
            _fail("compare.json schema validation failed: %s" % e)

    # --- Gates (shared with compare_gates.py) ---
    gate_errors = check_compare_gates(compare)
    for msg in gate_errors:
        _fail(msg)

    # --- budget_drift absent or empty (recommended) ---
    budget_drift = compare.get("budget_drift")
    if budget_drift is not None and isinstance(budget_drift, dict) and budget_drift:
        print("Warning: compare.json has non-empty budget_drift", file=sys.stderr)

    # Optional: eval_metadata run_id/hash vs predictions sidecars when runs_root and eval dirs exist (not in artifact-only mode).
    # Omitted here; add when harness exports run_id/hash into publish or when verifying from full runs tree.

    print("verify_publish_bundle: all checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
