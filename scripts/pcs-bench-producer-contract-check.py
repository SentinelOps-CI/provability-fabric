#!/usr/bin/env python3
"""Release-grade checks for PF pcs_bench_ingest producer output (PcsBenchIngest.v0 contract)."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

LABTRUST_FAILURE_FAMILIES = (
    "missing_handoff",
    "legacy_handoff_in_release_mode",
    "missing_registry",
    "wrong_admission_profile",
    "rejected_certificate",
    "certificate_status_rejected",
    "trace_hash_mismatch",
    "bundle_hash_mismatch",
    "registry_wrong_producer",
    "registry_disallowed_status",
    "missing_proof_obligation",
    "missing_lean_check_result",
    "failed_lean_check",
    "failed_lean_theorem",
    "unauthorized_lean_theorem",
    "scientific_memory_import_failure",
)

_ZERO_COMMIT = re.compile(r"^[0f]{40}$", re.IGNORECASE)


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def check_ingest(ingest: dict, *, bundle_dir: Path) -> list[str]:
    errors: list[str] = []
    if ingest.get("producer_id") != "provability-fabric":
        errors.append(f"producer_id={ingest.get('producer_id')!r}")
    if ingest.get("suite_id") != "pf-labtrust-admission-v0":
        errors.append(f"suite_id={ingest.get('suite_id')!r}")
    if ingest.get("workflow_id") != "hospital_lab.qc_release":
        errors.append(f"workflow_id={ingest.get('workflow_id')!r}")
    commit = ingest.get("source_commit", "")
    if not isinstance(commit, str) or len(commit) != 40 or _ZERO_COMMIT.match(commit):
        errors.append("source_commit must be a real 40-char git commit")
    for field in (
        "benchmark_runs",
        "coverage_reports",
        "failure_localization_reports",
        "explain_quality_reports",
        "commands",
    ):
        rows = ingest.get(field)
        if not isinstance(rows, list) or not rows:
            errors.append(f"{field} must be non-empty")
    profile = ingest.get("profile_coverage_reports")
    if not isinstance(profile, list) or not profile:
        errors.append("profile_coverage_reports must be non-empty for PF")
    refs = ingest.get("artifact_refs")
    if not isinstance(refs, list) or not refs:
        errors.append("artifact_refs must be non-empty")
    for index, cmd in enumerate(ingest.get("commands") or []):
        if not isinstance(cmd, dict):
            errors.append(f"commands[{index}] must be an object")
            continue
        line = cmd.get("command", "")
        if isinstance(line, str) and "\\" in line:
            errors.append(f"commands[{index}] must not contain backslashes")
        if isinstance(line, str) and "benchmarks/admission/labtrust_qc_release" not in line:
            errors.append(f"commands[{index}] must use repo-relative cases path")
    for index, ref in enumerate(refs or []):
        if not isinstance(ref, dict):
            continue
        path = ref.get("path", "")
        if isinstance(path, str) and "\\" in path:
            errors.append(f"artifact_refs[{index}].path must use forward slashes")
        if isinstance(path, str) and path:
            sidecar = bundle_dir / Path(path.replace("\\", "/"))
            if not sidecar.is_file():
                errors.append(f"artifact_refs[{index}] missing sidecar {path}")
    run_ids = {row.get("case_id") for row in ingest.get("benchmark_runs") or [] if isinstance(row, dict)}
    for case_id in LABTRUST_FAILURE_FAMILIES:
        if case_id not in run_ids:
            errors.append(f"benchmark_runs missing failure-family case {case_id!r}")
    if not any(cid in run_ids for cid in ("release_chain", "release_admission")):
        errors.append("benchmark_runs missing valid release case (release_chain or release_admission)")
    roles = {(r.get("artifact_type"), r.get("role")) for r in refs or [] if isinstance(r, dict)}
    if ("BenchmarkRun.v0", "primary") not in roles:
        errors.append("expected BenchmarkRun.v0 artifact_refs with role primary")
    if ("ProfileCoverageReport.v0", "ingest_bundle") not in roles:
        errors.append("expected ProfileCoverageReport.v0 artifact_refs with role ingest_bundle")
    return errors


def check_suite_metrics(bundle_dir: Path) -> list[str]:
    suite_path = bundle_dir / "admission_benchmark_suite.v0.json"
    if not suite_path.is_file():
        return [f"missing {suite_path.name}"]
    metrics = _load_json(suite_path).get("metrics") or {}
    errors: list[str] = []
    if metrics.get("valid_release_admission_rate") != 1.0:
        errors.append(f"valid_release_admission_rate={metrics.get('valid_release_admission_rate')}")
    if (metrics.get("invalid_release_rejection_rate") or 0) < 1.0:
        errors.append(f"invalid_release_rejection_rate={metrics.get('invalid_release_rejection_rate')}")
    if (metrics.get("failure_localization_accuracy") or 0) < 0.85:
        errors.append(f"failure_localization_accuracy={metrics.get('failure_localization_accuracy')}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ingest", type=Path, required=True)
    parser.add_argument("--bundle-dir", type=Path, default=None)
    args = parser.parse_args()
    ingest_path = args.ingest.resolve()
    bundle_dir = (args.bundle_dir or ingest_path.parent).resolve()
    if not ingest_path.is_file():
        print(f"missing ingest: {ingest_path}", file=sys.stderr)
        return 1
    ingest = _load_json(ingest_path)
    errors = check_ingest(ingest, bundle_dir=bundle_dir)
    errors.extend(check_suite_metrics(bundle_dir))
    if errors:
        for err in errors:
            print(f"FAIL {err}", file=sys.stderr)
        return 1
    print(f"OK producer contract: {ingest_path.name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
