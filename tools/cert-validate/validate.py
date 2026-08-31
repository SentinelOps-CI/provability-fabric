#!/usr/bin/env python3
"""
Certificate validation tool.

Runtime certificates are validated against the external CERT-V1 schema.
TRACE-REPLAY-KIT trace_replay certificates are validated against the checked-in
Evidence v0.2 trace-replay schema.
"""

from __future__ import annotations

import argparse
import glob
import json
import sys
from pathlib import Path

from jsonschema import Draft202012Validator, ValidationError, validate

_TOOL_DIR = Path(__file__).resolve().parent
if str(_TOOL_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOL_DIR))
from format_check import FormatCheckUnavailable, compile_trace_replay_validator  # noqa: E402

VALID = 0
INVALID = 1
OPERATIONAL_ERROR = 2
SKIPPED = 3

REPO_ROOT = Path(__file__).resolve().parents[2]
TRACE_REPLAY_SCHEMA_PATH = (
    REPO_ROOT / "specs" / "evidence" / "v0.2" / "schemas" / "trace-replay-cert.schema.json"
)
DEFAULT_RUNTIME_SCHEMA_PATH = REPO_ROOT / "external" / "CERT-V1" / "schema" / "cert-v1.schema.json"
_TRACE_REPLAY_VALIDATOR: Draft202012Validator | None = None
_RUNTIME_SCHEMAS: dict[str, object] = {}


def load_schema(schema_path: str | Path, missing_hint: str | None = None):
    """Load a JSON schema from disk; return None when the path is absent."""
    path = Path(schema_path)
    if not path.exists():
        print(f"Schema not found at {path}.")
        if missing_hint:
            print(missing_hint)
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"error loading schema from {path}: {exc}") from exc


def trace_replay_validator() -> Draft202012Validator:
    """Load and compile the normative trace_replay schema once."""
    global _TRACE_REPLAY_VALIDATOR
    if _TRACE_REPLAY_VALIDATOR is not None:
        return _TRACE_REPLAY_VALIDATOR
    schema = load_schema(TRACE_REPLAY_SCHEMA_PATH)
    if schema is None:
        raise RuntimeError(f"trace replay schema missing at {TRACE_REPLAY_SCHEMA_PATH}")
    try:
        _TRACE_REPLAY_VALIDATOR = compile_trace_replay_validator(schema)
    except FormatCheckUnavailable as exc:
        raise RuntimeError(str(exc)) from exc
    return _TRACE_REPLAY_VALIDATOR


def runtime_schema(schema_path: str):
    """Load a runtime certificate schema lazily so trace-only validation is independent."""
    if schema_path in _RUNTIME_SCHEMAS:
        return _RUNTIME_SCHEMAS[schema_path]
    schema = load_schema(
        schema_path,
        "Clone external/CERT-V1 for runtime certificate validation.",
    )
    if schema is not None:
        _RUNTIME_SCHEMAS[schema_path] = schema
    return schema


def validate_trace_replay(file_path: str, data: object) -> int:
    """Validate a trace replay certificate against the Evidence v0.2 schema."""
    try:
        trace_replay_validator().validate(data)
        print(f"✓ {file_path} (trace_replay)")
        return VALID
    except ValidationError as exc:
        print(f"✗ {file_path}: {exc.message}")
        return INVALID
    except Exception as exc:
        print(f"✗ {file_path}: trace replay schema error - {exc}")
        return OPERATIONAL_ERROR


def validate_file(file_path: str, schema_path: str, allow_missing_schema: bool) -> int:
    """Validate one JSON certificate and return a stable exit-class code."""
    try:
        data = json.loads(Path(file_path).read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"✗ {file_path}: Invalid JSON - {exc}")
        return INVALID
    except (OSError, UnicodeError) as exc:
        print(f"✗ {file_path}: file error - {exc}")
        return OPERATIONAL_ERROR

    if isinstance(data, dict) and data.get("cert_type") == "trace_replay":
        return validate_trace_replay(file_path, data)

    try:
        schema = runtime_schema(schema_path)
    except Exception as exc:
        print(f"✗ {file_path}: runtime schema error - {exc}")
        return OPERATIONAL_ERROR

    if schema is None:
        if allow_missing_schema:
            print(f"↷ {file_path}: runtime schema unavailable; skipped by explicit option")
            return SKIPPED
        print(f"✗ {file_path}: runtime certificate schema unavailable")
        return OPERATIONAL_ERROR

    try:
        validate(instance=data, schema=schema)
        print(f"✓ {file_path}")
        return VALID
    except ValidationError as exc:
        print(f"✗ {file_path}: {exc.message}")
        return INVALID
    except Exception as exc:
        print(f"✗ {file_path}: runtime schema validation error - {exc}")
        return OPERATIONAL_ERROR


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Validate runtime CERT-V1 and trace replay JSON certificates"
    )
    parser.add_argument(
        "files", nargs="+", help="JSON files or glob patterns to validate"
    )
    parser.add_argument(
        "--schema",
        default=str(DEFAULT_RUNTIME_SCHEMA_PATH),
        help="Path to runtime CERT-V1 schema file",
    )
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose output")
    parser.add_argument(
        "--allow-missing-schema",
        action="store_true",
        help="Skip runtime certificates when their schema is unavailable",
    )
    args = parser.parse_args()

    all_files: list[str] = []
    for pattern in args.files:
        if "*" in pattern or "?" in pattern:
            all_files.extend(glob.glob(pattern, recursive=True))
        else:
            all_files.append(pattern)

    json_files = [path for path in all_files if path.endswith(".json")]
    if not json_files:
        print("No JSON files resolved from the supplied paths or patterns")
        return OPERATIONAL_ERROR

    if args.verbose:
        print(f"Found {len(json_files)} JSON files to validate")

    invalid_count = 0
    operational_count = 0
    passed_count = 0
    skipped_count = 0
    for file_path in json_files:
        if not Path(file_path).exists():
            print(f"✗ {file_path}: file does not exist")
            operational_count += 1
            continue
        status = validate_file(file_path, args.schema, args.allow_missing_schema)
        if status == VALID:
            passed_count += 1
        elif status == INVALID:
            invalid_count += 1
        elif status == SKIPPED:
            skipped_count += 1
        else:
            operational_count += 1

    print("\nValidation Summary:")
    print(f"  Total files: {len(json_files)}")
    print(f"  Passed: {passed_count}")
    print(f"  Invalid: {invalid_count}")
    print(f"  Skipped: {skipped_count}")
    print(f"  Operational errors: {operational_count}")

    if operational_count:
        print(f"\nValidation could not complete for {operational_count} file(s)")
        return OPERATIONAL_ERROR
    if invalid_count:
        print(f"\nValidation failed for {invalid_count} invalid file(s)")
        return INVALID
    if skipped_count:
        print(f"\nValidation completed with {skipped_count} explicit skip(s)")
        return VALID
    print("\nAll files validated successfully")
    return VALID


if __name__ == "__main__":
    sys.exit(main())
