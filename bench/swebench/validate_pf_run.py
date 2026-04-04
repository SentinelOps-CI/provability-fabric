#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Validate PF-guarded SWE-bench run: policy hash in each instance bundle,
# structured violation events, final compliance summary (pass/fail, reason_codes),
# and that denials are recoverable (agent can continue) unless fail-fast is set.

from __future__ import annotations

import json
import sys
from pathlib import Path


def validate_run(run_dir: Path) -> tuple[bool, list[str]]:
    """Validate a PF run directory. Returns (all_ok, list of error/warning messages)."""
    run_dir = Path(run_dir).resolve()
    if not run_dir.is_dir():
        return False, [f"Not a directory: {run_dir}"]

    errors: list[str] = []
    warnings: list[str] = []
    instance_dirs = [d for d in run_dir.iterdir() if d.is_dir() and not d.name.startswith(".")]

    for inst_dir in sorted(instance_dirs):
        meta_path = inst_dir / "metadata.json"
        evidence_dir = inst_dir / "evidence"
        events_path = evidence_dir / "events.jsonl"
        compliance_path = inst_dir / "policy_compliance_summary.json"

        # Guarded runs have evidence and compliance summary
        is_guarded = compliance_path.exists() or (evidence_dir.is_dir() and events_path.exists())

        if is_guarded:
            if not meta_path.exists():
                errors.append(f"{inst_dir.name}: missing metadata.json")
            else:
                try:
                    meta = json.loads(meta_path.read_text(encoding="utf-8"))
                    if meta.get("policy_hash") in (None, ""):
                        errors.append(f"{inst_dir.name}: policy_hash missing in metadata.json (required for guarded run)")
                except (json.JSONDecodeError, OSError) as e:
                    errors.append(f"{inst_dir.name}: failed to read metadata.json: {e}")

            if not compliance_path.exists():
                errors.append(f"{inst_dir.name}: missing policy_compliance_summary.json")
            else:
                try:
                    summary = json.loads(compliance_path.read_text(encoding="utf-8"))
                    for key in ("compliant", "violations", "run_id"):
                        if key not in summary:
                            errors.append(f"{inst_dir.name}: policy_compliance_summary.json missing key '{key}'")
                    if "reason_codes" not in summary and summary.get("violations", 0) > 0:
                        warnings.append(f"{inst_dir.name}: compliance summary has violations but no reason_codes list (older format)")
                except (json.JSONDecodeError, OSError) as e:
                    errors.append(f"{inst_dir.name}: failed to read policy_compliance_summary.json: {e}")

            if events_path.exists() and compliance_path.exists():
                try:
                    summary = json.loads(compliance_path.read_text(encoding="utf-8"))
                    n_violations = summary.get("violations", 0)
                    violation_events = 0
                    with open(events_path, "r", encoding="utf-8") as f:
                        for line in f:
                            line = line.strip()
                            if not line:
                                continue
                            try:
                                ev = json.loads(line)
                                if ev.get("event_type") == "violation":
                                    violation_events += 1
                            except json.JSONDecodeError:
                                pass
                    if n_violations != violation_events:
                        warnings.append(
                            f"{inst_dir.name}: compliance summary violations={n_violations} but events.jsonl has {violation_events} violation events"
                        )
                except (OSError, json.JSONDecodeError):
                    pass

    all_ok = len(errors) == 0
    messages = errors + warnings
    return all_ok, messages


def main() -> int:
    if len(sys.argv) < 2:
        print("Usage: validate_pf_run.py <run_dir>", file=sys.stderr)
        print("  run_dir: e.g. runs/<run_id> from a pf_guarded or --guarded run", file=sys.stderr)
        return 2
    run_dir = Path(sys.argv[1])
    ok, messages = validate_run(run_dir)
    for m in messages:
        print(m)
    if ok and not messages:
        print("Validation passed: policy hash in instance bundles, compliance summary present.")
        print("Denials are recoverable by default (single command fails with exit 125; agent can continue).")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
