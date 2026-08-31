#!/usr/bin/env python3
"""Fail-closed date-time format checking for trace-replay certificates."""

from __future__ import annotations

import importlib.util

from jsonschema import Draft202012Validator, FormatChecker, ValidationError

_DATE_TIME_PROBE_SCHEMA = {"type": "string", "format": "date-time"}
_INVALID_DATE_TIME_PROBE = "not-a-timestamp"


class FormatCheckUnavailable(RuntimeError):
    """Raised when date-time format checking cannot be enforced."""


def require_date_time_format_checker() -> FormatChecker:
    """Return a FormatChecker that actually rejects invalid date-time values.

    jsonschema treats format assertions as optional unless a working checker
    backend is installed. Missing rfc3339-validator must not collapse into a
    successful validation of ``not-a-timestamp``.
    """
    if importlib.util.find_spec("rfc3339_validator") is None:
        raise FormatCheckUnavailable(
            "rfc3339-validator is required for fail-closed date-time format "
            "checking; install tools/cert-validate/requirements.txt"
        )
    checker = FormatChecker()
    probe = Draft202012Validator(_DATE_TIME_PROBE_SCHEMA, format_checker=checker)
    try:
        probe.validate(_INVALID_DATE_TIME_PROBE)
    except ValidationError:
        return checker
    raise FormatCheckUnavailable(
        "date-time format checking did not reject an invalid timestamp; "
        "install rfc3339-validator and retry"
    )


def compile_trace_replay_validator(schema: object) -> Draft202012Validator:
    """Compile a trace-replay schema with fail-closed date-time checking."""
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(
        schema, format_checker=require_date_time_format_checker()
    )
