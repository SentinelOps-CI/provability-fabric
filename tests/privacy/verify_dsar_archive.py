#!/usr/bin/env python3
"""Validate the actual decrypted synthetic DSAR export, not a separate fixture.

The exporter currently synthesizes records; this checker establishes archive
integrity, schema/tenant binding, and redaction of declared fields only.
It is not evidence that live ledger data have been exported or redacted.
"""

from __future__ import annotations

import argparse
import json
import math
import zipfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


class InvalidDSAR(ValueError):
    """A decrypted export does not satisfy the synthetic DSAR contract."""


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidDSAR(message)


def _unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for key, value in pairs:
        _require(key not in obj, f"duplicate JSON field: {key}")
        obj[key] = value
    return obj


def _exact_fields(obj: Any, required: set[str], optional: set[str] = frozenset()) -> None:
    _require(isinstance(obj, dict), "record must be an object")
    _require(required <= obj.keys(), f"missing fields: {sorted(required - obj.keys())}")
    _require(obj.keys() <= required | optional, f"unexpected fields: {sorted(obj.keys() - required - optional)}")


def _timestamp(raw: Any) -> datetime:
    _require(isinstance(raw, str), "timestamp must be a string")
    try:
        value = datetime.fromisoformat(raw.replace("Z", "+00:00"))
    except ValueError as exc:
        raise InvalidDSAR(f"invalid timestamp: {raw!r}") from exc
    _require(value.tzinfo is not None and value.utcoffset() is not None, "timestamp must be timezone-aware")
    return value.astimezone(timezone.utc)


def validate_payload(
    raw: bytes, *, expected_tenant: str, after_date: str, expected_count: int = 2
) -> dict[str, Any]:
    """Validate a mock export's typed fields, tenant, dates, and record counts."""
    _require(len(raw) <= 10_000_000, "JSON payload exceeds size limit")
    try:
        obj = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_unique_pairs,
            parse_constant=lambda x: (_ for _ in ()).throw(InvalidDSAR(f"invalid number: {x}")),
        )
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise InvalidDSAR("invalid UTF-8 JSON payload") from exc

    _exact_fields(obj, {"tenant_id", "export_date", "usage_events", "capsules", "metadata"})
    _require(obj["tenant_id"] == expected_tenant, "export tenant mismatch")
    _timestamp(obj["export_date"])
    threshold = _timestamp(after_date + "T00:00:00Z")

    metadata = obj["metadata"]
    _exact_fields(metadata, {"export_version", "pii_redacted", "encrypted", "after_date"})
    _require(metadata["export_version"] == "1.0", "unexpected export format")
    _require(metadata["pii_redacted"] is True, "redaction flag missing")
    _require(metadata["encrypted"] is True, "encryption flag missing")
    _require(_timestamp(metadata["after_date"]) == threshold, "date filter mismatch")

    for field in ("usage_events", "capsules"):
        records = obj[field]
        _require(isinstance(records, list) and len(records) == expected_count, f"unexpected {field} count")
        for record in records:
            if field == "usage_events":
                _exact_fields(record, {"id", "tenant_id", "cpu_ms", "net_bytes", "timestamp"})
                _require(type(record["cpu_ms"]) is int and record["cpu_ms"] >= 0, "invalid CPU measurement")
                _require(type(record["net_bytes"]) is int and record["net_bytes"] >= 0, "invalid network measurement")
                observed_date = _timestamp(record["timestamp"])
            else:
                _exact_fields(
                    record,
                    {"id", "tenant_id", "hash", "spec_sig", "risk_score", "created_at", "updated_at"},
                    {"reason"},
                )
                for name in ("hash", "spec_sig"):
                    _require(isinstance(record[name], str) and bool(record[name]), f"invalid {name}")
                score = record["risk_score"]
                _require(
                    type(score) in (float, int) and math.isfinite(score) and 0 <= score <= 1,
                    "invalid risk score",
                )
                if "reason" in record:
                    _require(isinstance(record["reason"], str), "invalid reason")
                observed_date = _timestamp(record["created_at"])
                _require(_timestamp(record["updated_at"]) >= observed_date, "inverted capsule timestamps")
            _require(isinstance(record["id"], str) and bool(record["id"]), "invalid record ID")
            _require(record["tenant_id"] == expected_tenant, "cross-tenant record")
            _require(observed_date > threshold, "record violates after-date filter")
    return obj


def validate_archive(
    path: Path, *, expected_tenant: str, after_date: str, expected_count: int = 2
) -> dict[str, Any]:
    """Read exactly one bounded, well-formed JSON member from a decrypted ZIP."""
    try:
        with zipfile.ZipFile(path) as archive:
            entries = archive.infolist()
            _require(len(entries) == 1 and entries[0].filename == "dsar-data.json", "unexpected ZIP members")
            _require(not entries[0].is_dir(), "DSAR member is a directory")
            _require(entries[0].file_size <= 10_000_000, "DSAR member exceeds size limit")
            _require(archive.testzip() is None, "ZIP integrity failure")
            raw = archive.read(entries[0])
    except (OSError, zipfile.BadZipFile, RuntimeError) as exc:
        raise InvalidDSAR(f"unreadable or corrupt ZIP archive ({type(exc).__name__}: {exc})") from exc
    return validate_payload(
        raw, expected_tenant=expected_tenant, after_date=after_date, expected_count=expected_count
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="decrypted ZIP file")
    parser.add_argument("--tenant", required=True)
    parser.add_argument("--after", dest="after_date", required=True, help="YYYY-MM-DD")
    parser.add_argument("--expected-count", type=int, default=2)
    args = parser.parse_args()
    try:
        validate_archive(
            args.archive,
            expected_tenant=args.tenant,
            after_date=args.after_date,
            expected_count=args.expected_count,
        )
    except (InvalidDSAR, OSError, ValueError) as exc:
        parser.exit(1, f"DSAR archive validation failed: {exc}\n")
    print("Decrypted synthetic DSAR archive verified: ZIP integrity, typed fields, tenant and filter")


if __name__ == "__main__":
    main()
