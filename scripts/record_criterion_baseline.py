#!/usr/bin/env python3
"""Update Criterion baseline metadata without discarding the existing record.

The benchmark itself must complete successfully before invoking this helper.
A malformed or incomplete metadata table aborts without changing the file.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import platform
import re
import subprocess
import tempfile

SHA_RE = re.compile(r"[0-9a-f]{40}\Z")
FIELDS = {
    "Last refresh SHA": "sha",
    "Last refresh date (UTC)": "date",
    "Last refresh machine": "machine",
}


def update_baseline_document(text: str, *, sha: str, date: str, machine: str) -> str:
    """Replace three metadata cells, preserving all unrelated documentation.

    Raise ValueError for missing/duplicate fields or invalid metadata. This
    prevents a partial or misleading baseline history from being published.
    """
    if not SHA_RE.fullmatch(sha):
        raise ValueError("git SHA must be a full lowercase hexadecimal commit ID")
    if not re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", date):
        raise ValueError("date must be an ISO 8601 UTC timestamp")
    try:
        datetime.strptime(date, "%Y-%m-%dT%H:%M:%SZ")
    except ValueError as exc:
        raise ValueError("invalid UTC calendar timestamp") from exc
    if not machine.strip() or any(c in machine for c in "\r\n|"):
        raise ValueError("machine description contains invalid characters")

    values = {"sha": f"`{sha}`", "date": date, "machine": machine}
    updated = text
    for label, name in FIELDS.items():
        pattern = re.compile(
            r"(?m)^(\| " + re.escape(label) + r" \| )([^|\r\n]*)( \|)$"
        )
        updated, count = pattern.subn(
            lambda match: f"{match.group(1)}{values[name]}{match.group(3)}",
            updated,
        )
        if count != 1:
            raise ValueError(
                f"baseline metadata must contain exactly one {label!r} row"
            )
    return updated


def record_baseline(path: Path, *, sha: str, date: str, machine: str) -> None:
    """Atomically replace validated metadata in an existing Markdown record."""
    if not path.is_file() or path.is_symlink():
        raise ValueError(f"baseline record must be an existing regular file: {path}")
    original = path.read_text(encoding="utf-8")
    updated = update_baseline_document(original, sha=sha, date=date, machine=machine)

    temp_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "w", encoding="utf-8", newline="\n", dir=path.parent,
            prefix=".baseline-", delete=False,
        ) as handle:
            temp_path = Path(handle.name)
            handle.write(updated)
            handle.flush()
            os.fsync(handle.fileno())
        temp_path.chmod(path.stat().st_mode & 0o777)
        os.replace(temp_path, path)
    finally:
        if temp_path is not None:
            temp_path.unlink(missing_ok=True)


def main() -> None:
    """Capture the checked-out commit, UTC timestamp and runner identity."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", type=Path, default=Path("bench/BASELINE.md"))
    args = parser.parse_args()
    sha = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    date = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    host = platform.uname()
    machine = f"{host.system} {host.release} {host.machine}"
    record_baseline(args.path, sha=sha, date=date, machine=machine)
    print(f"Updated {args.path} for {sha} at {date}")


if __name__ == "__main__":
    main()
