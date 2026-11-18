#!/usr/bin/env python3
"""Record and validate execution-derived TRUST-FIRE CI phase evidence.

This module reports *GitHub Actions step outcomes*, not formal proof verdicts.
Phase outcomes and timing come from the runner's step context and outputs. The
validator independently recomputes the verdict and checks phase coverage and
run provenance. Nothing in this script independently attests the runner.

No third-party Python dependencies are needed.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Mapping

PHASES = ("2", "3", "6")
SCHEMA_VERSION = 1
SUITE = "TRUST-FIRE GA CI Subset"
SOURCE = "github_actions_step_outcome"
COMMANDS = {
    "2": "python tests/privacy/privacy_burn_down.py",
    "3": "python tests/security/malicious_adapter_test.py",
    "6": "python tests/compliance/evidence_kpi_audit.py",
}
VALID_OUTCOMES = {"success", "failure", "skipped", "cancelled", "timed_out", ""}
_SHA_PATTERN = re.compile(r"[0-9a-f]{40}\Z")


class EvidenceError(ValueError):
    """A report, selection, runner value, or provenance check is invalid."""


def parse_phases(raw: str) -> tuple[str, ...]:
    """Parse an exact comma-separated selection, rejecting duplicates and noise."""
    if not isinstance(raw, str) or not raw.strip():
        raise EvidenceError("phase selection must be nonempty")
    parts = [part.strip() for part in raw.split(",")]
    if any(part not in PHASES for part in parts):
        raise EvidenceError("only phases 2, 3, and 6 are supported")
    if len(parts) != len(set(parts)):
        raise EvidenceError("duplicate TRUST-FIRE phase")
    return tuple(p for p in PHASES if p in parts)


def utc_timestamp(value: datetime | None = None) -> str:
    """Emit a second-resolution UTC RFC 3339 timestamp."""
    current = value if value is not None else datetime.now(timezone.utc)
    if current.tzinfo is None:
        raise EvidenceError("naive timestamps are not accepted")
    return current.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def parse_timestamp(raw: Any, *, field: str) -> datetime:
    """Enforce canonical, timezone-aware UTC timestamps for CI events."""
    if not isinstance(raw, str) or not re.fullmatch(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", raw):
        raise EvidenceError(f"{field}: expected canonical UTC timestamp")
    try:
        instant = datetime.strptime(raw, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except ValueError as exc:
        raise EvidenceError(f"{field}: invalid UTC timestamp") from exc
    return instant


def require_positive_integer(raw: Any, *, field: str) -> int:
    """Reject booleans, fractional values, zero, and malformed IDs."""
    if isinstance(raw, bool):
        raise EvidenceError(f"{field}: boolean is not an integer ID")
    try:
        number = int(raw)
    except (ValueError, TypeError) as exc:
        raise EvidenceError(f"{field}: expected positive integer") from exc
    if str(number) != str(raw) or number < 1:
        raise EvidenceError(f"{field}: expected positive canonical integer")
    return number


def validate_context(context: Mapping[str, Any]) -> dict[str, Any]:
    """Validate exact GitHub run identifiers; no guessed defaults."""
    repository = context.get("repository")
    if not isinstance(repository, str) or not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
        raise EvidenceError("invalid GITHUB_REPOSITORY")
    sha = context.get("commit_sha")
    if not isinstance(sha, str) or not _SHA_PATTERN.fullmatch(sha):
        raise EvidenceError("invalid GITHUB_SHA")
    return {
        "repository": repository,
        "commit_sha": sha,
        "run_id": require_positive_integer(context.get("run_id"), field="run_id"),
        "run_attempt": require_positive_integer(context.get("run_attempt"), field="run_attempt"),
    }


def context_from_environment(env: Mapping[str, str]) -> dict[str, Any]:
    """Resolve provenance from runner-populated GitHub environment variables."""
    return validate_context({
        "repository": env.get("GITHUB_REPOSITORY"),
        "commit_sha": env.get("GITHUB_SHA"),
        "run_id": env.get("GITHUB_RUN_ID"),
        "run_attempt": env.get("GITHUB_RUN_ATTEMPT"),
    })


def phase_record(phase: str, *, requested: bool, outcome: str,
                 started_at: str | None, completed_at: str | None) -> dict[str, Any]:
    """Compute a single phase status from outcome and clock evidence."""
    if phase not in PHASES or outcome not in VALID_OUTCOMES:
        raise EvidenceError("unknown phase or GitHub step outcome")
    start: datetime | None = None
    end: datetime | None = None
    if started_at:
        start = parse_timestamp(started_at, field=f"phase_{phase}.started_at")
    if completed_at:
        end = parse_timestamp(completed_at, field=f"phase_{phase}.completed_at")
    valid_interval = start is not None and end is not None and end >= start
    if requested:
        status = "PASS" if outcome == "success" and valid_interval else "FAIL"
    else:
        status = "SKIP" if outcome in ("skipped", "") and start is None and end is None else "FAIL"
    return {
        "requested": requested,
        "status": status,
        "step_outcome": outcome,
        "started_at": started_at or None,
        "completed_at": completed_at or None,
        "command": COMMANDS[phase],
    }


def overall_status(requested: tuple[str, ...], records: Mapping[str, Mapping[str, Any]]) -> str:
    """A full PASS needs all three requested phases to execute successfully."""
    if any(records[f"phase_{p}"]["status"] == "FAIL" for p in PHASES):
        return "FAIL"
    if requested != PHASES:
        return "PARTIAL"
    return "PASS" if all(records[f"phase_{p}"]["status"] == "PASS" for p in PHASES) else "FAIL"


def build_report(*, raw_selection: str, context: Mapping[str, Any],
                 selection_started_at: str, step_data: Mapping[str, Mapping[str, str]],
                 completed_at: str | None = None) -> dict[str, Any]:
    """Create a report whose status is derived only from actual step outcomes."""
    selected = parse_phases(raw_selection)
    provenance = validate_context(context)
    started = parse_timestamp(selection_started_at, field="selection_started_at")
    finished_string = completed_at if completed_at is not None else utc_timestamp()
    finished = parse_timestamp(finished_string, field="end_time")
    if finished < started:
        raise EvidenceError("report end precedes selection")
    records = {}
    for phase in PHASES:
        phase_data = step_data.get(phase, {})
        record = phase_record(
            phase,
            requested=phase in selected,
            outcome=phase_data.get("outcome", ""),
            started_at=phase_data.get("started_at", ""),
            completed_at=phase_data.get("completed_at", ""),
        )
        if record["started_at"] and parse_timestamp(record["started_at"], field="phase.start") < started:
            raise EvidenceError(f"phase {phase} starts before phase selection")
        if record["completed_at"] and parse_timestamp(record["completed_at"], field="phase.end") > finished:
            raise EvidenceError(f"phase {phase} ends after report completion")
        records[f"phase_{phase}"] = record
    return {
        "schema_version": SCHEMA_VERSION,
        "test_suite": SUITE,
        "evidence_source": SOURCE,
        **provenance,
        "requested_phases": list(selected),
        "start_time": selection_started_at,
        "end_time": finished_string,
        "duration_seconds": int((finished - started).total_seconds()),
        "phase_results": records,
        "overall_status": overall_status(selected, records),
    }


def _no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        if key in obj:
            raise EvidenceError(f"duplicate JSON key: {key}")
        obj[key] = value
    return obj


def _reject_json_constant(value: str) -> None:
    raise EvidenceError(f"nonfinite JSON constant: {value}")


def read_report(path: str | Path) -> dict[str, Any]:
    """Parse a bounded JSON report and reject ambiguous duplicate keys."""
    content = Path(path).read_bytes()
    if len(content) > 65536:
        raise EvidenceError("report exceeds 64 KiB")
    obj = json.loads(content, object_pairs_hook=_no_duplicate_keys,
                     parse_constant=_reject_json_constant)
    if not isinstance(obj, dict):
        raise EvidenceError("report must be a JSON object")
    return obj


def validate_report(report: Mapping[str, Any], *, expected_context: Mapping[str, Any],
                    expected_selection: str) -> None:
    """Independently re-derive all statuses, coverage, times, and provenance."""
    expected = validate_context(expected_context)
    if type(report.get("schema_version")) is not int or report["schema_version"] != SCHEMA_VERSION:
        raise EvidenceError("unsupported evidence schema version")
    if report.get("test_suite") != SUITE or report.get("evidence_source") != SOURCE:
        raise EvidenceError("unexpected test suite or evidence source")
    for key, value in expected.items():
        if report.get(key) != value or type(report.get(key)) is not type(value):
            raise EvidenceError(f"provenance mismatch: {key}")
    phases = parse_phases(expected_selection)
    if report.get("requested_phases") != list(phases):
        raise EvidenceError("selected phases do not match the workflow input")
    started = parse_timestamp(report.get("start_time"), field="start_time")
    ended = parse_timestamp(report.get("end_time"), field="end_time")
    if ended < started:
        raise EvidenceError("report duration is negative")
    duration = int((ended - started).total_seconds())
    if type(report.get("duration_seconds")) is not int or report["duration_seconds"] != duration:
        raise EvidenceError("reported duration does not match timestamps")
    records = report.get("phase_results")
    if not isinstance(records, dict) or set(records) != {f"phase_{p}" for p in PHASES}:
        raise EvidenceError("missing or unexpected phase record")
    recomputed: dict[str, dict[str, Any]] = {}
    for p in PHASES:
        actual = records[f"phase_{p}"]
        if not isinstance(actual, dict):
            raise EvidenceError("phase record must be an object")
        expected_record = phase_record(
            p, requested=p in phases, outcome=actual.get("step_outcome"),
            started_at=actual.get("started_at"), completed_at=actual.get("completed_at"),
        )
        if actual != expected_record:
            raise EvidenceError(f"unfaithful phase {p} record")
        for field in ("started_at", "completed_at"):
            if actual[field]:
                t = parse_timestamp(actual[field], field=f"phase_{p}.{field}")
                if t < started or t > ended:
                    raise EvidenceError(f"phase {p} timestamp outside report interval")
        recomputed[f"phase_{p}"] = expected_record
    expected_status = overall_status(phases, recomputed)
    if report.get("overall_status") != expected_status:
        raise EvidenceError("overall verdict is not derived from phases")
    if phases != PHASES or expected_status != "PASS":
        raise EvidenceError("the full TRUST-FIRE 2/3/6 gate did not pass")


def _environment_steps(env: Mapping[str, str]) -> dict[str, dict[str, str]]:
    return {p: {
        "outcome": env.get(f"PHASE_{p}_OUTCOME", ""),
        "started_at": env.get(f"PHASE_{p}_STARTED_AT", ""),
        "completed_at": env.get(f"PHASE_{p}_COMPLETED_AT", ""),
    } for p in PHASES}


def main(argv: list[str] | None = None, *, env: Mapping[str, str] | None = None) -> int:
    """Entrypoint for selection, report creation, and independent verification."""
    e = os.environ if env is None else env
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    select = sub.add_parser("select", help="validate phases and write GITHUB_OUTPUT")
    select.add_argument("--output", required=True)
    report = sub.add_parser("report", help="derive report from GitHub Actions step outcomes")
    report.add_argument("--output", required=True)
    gate = sub.add_parser("gate", help="independently validate a report and fail closed")
    gate.add_argument("--report", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "select":
            phases = parse_phases(e.get("TRUST_FIRE_PHASES", ""))
            output = f"phase_ids={json.dumps(list(phases), separators=(',', ':'))}\nstarted_at={utc_timestamp()}\n"
            with Path(args.output).open("a", encoding="utf-8") as fh:
                fh.write(output)
            return 0
        context = context_from_environment(e)
        if args.command == "report":
            result = build_report(
                raw_selection=e.get("TRUST_FIRE_PHASES", ""), context=context,
                selection_started_at=e.get("TRUST_FIRE_STARTED_AT", ""),
                step_data=_environment_steps(e),
            )
            Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
            print(f"TRUST-FIRE report status: {result['overall_status']}")
            return 0
        evidence = read_report(args.report)
        validate_report(evidence, expected_context=context, expected_selection=e.get("TRUST_FIRE_PHASES", ""))
        print("TRUST-FIRE 2/3/6 full-suite execution evidence gate passed")
        return 0
    except (EvidenceError, OSError, json.JSONDecodeError, TypeError, ValueError) as exc:
        print(f"TRUST-FIRE evidence error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
