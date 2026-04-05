#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Run verification tests that do not require WSL/Linux or agent runs.
# Use after implementing Phase 0-4 to confirm: verifier, ledger, stress summary, stress alerts.

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_EXPERIMENTS = _SCRIPT_DIR.parent
_FIXTURE_PUBLISH = _EXPERIMENTS / "fixtures" / "verify_publish_bundle" / "publish"
_FIXTURE_COMPARE = _EXPERIMENTS / "fixtures" / "verify_publish_bundle" / "compare.json"


def _run(cmd: list[str], name: str) -> bool:
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=_SCRIPT_DIR.parent.parent)
    if r.returncode != 0:
        print("FAIL %s: %s" % (name, r.stderr or r.stdout), file=sys.stderr)
        return False
    return True


def main() -> int:
    failed = []

    # 1. verify_publish_bundle on fixture
    if not _run(
        [
            sys.executable,
            str(_SCRIPT_DIR / "verify_publish_bundle.py"),
            "--publish-dir", str(_FIXTURE_PUBLISH),
            "--compare-json", str(_FIXTURE_COMPARE),
            "--skip-run-dir-check",
        ],
        "verify_publish_bundle",
    ):
        failed.append("verify_publish_bundle")

    if not _run(
        [sys.executable, "-m", "pytest", "tests/test_publish_manifest.py", "-q", "--tb=no"],
        "pytest test_publish_manifest",
    ):
        failed.append("pytest test_publish_manifest")

    # 2. append_scale_results_ledger (append one row)
    if not _run(
        [
            sys.executable,
            str(_SCRIPT_DIR / "append_scale_results_ledger.py"),
            "--compare-json", str(_FIXTURE_COMPARE),
            "--experiment-id", "exp-step2-lite-smoke",
            "--pf-commit", "test-commit",
        ],
        "append_scale_results_ledger",
    ):
        failed.append("append_scale_results_ledger")

    # 3. summarize_stress_run minimal (schema_version + provenance)
    stress_out = _EXPERIMENTS / "fixtures" / "stress_summary_verification_test.json"
    stress_baseline = _EXPERIMENTS / "fixtures" / "stress_baseline"
    stress_pf = _EXPERIMENTS / "fixtures" / "stress_pf"
    stress_baseline.mkdir(parents=True, exist_ok=True)
    stress_pf.mkdir(parents=True, exist_ok=True)
    if not _run(
        [
            sys.executable,
            str(_SCRIPT_DIR / "summarize_stress_run.py"),
            "--baseline-run-dir", str(stress_baseline),
            "--pf-run-dir", str(stress_pf),
            "--compare-json", str(_FIXTURE_COMPARE),
            "--out", str(stress_out),
            "--pf-commit", "test-commit",
        ],
        "summarize_stress_run",
    ):
        failed.append("summarize_stress_run")
    else:
        try:
            data = json.loads(stress_out.read_text(encoding="utf-8"))
            if data.get("schema_version") != "1.0":
                failed.append("summarize_stress_run (schema_version)")
            if data.get("pf_commit") != "test-commit":
                failed.append("summarize_stress_run (pf_commit)")
        except (OSError, json.JSONDecodeError):
            failed.append("summarize_stress_run (read output)")

    # 4. Stress alert logic (all thresholds OK on fixture) via single script
    if not _run(
        [
            sys.executable,
            str(_SCRIPT_DIR / "check_stress_alerts.py"),
            "--stress-summary", str(stress_out),
            "--compare-json", str(_FIXTURE_COMPARE),
        ],
        "check_stress_alerts",
    ):
        failed.append("check_stress_alerts")

    if failed:
        print("Verification tests failed: %s" % failed, file=sys.stderr)
        return 1
    print("All verification tests passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
