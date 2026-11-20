#!/usr/bin/env python3
"""Read-only APOLLO proposal inventory.

The scan is lexical, and remote suggestions are untrusted. No candidate is
applied, compiled, committed, or represented as a checked Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
from typing import Any
from urllib.parse import urlsplit

import requests

SKIP_DIRECTORIES = frozenset({".git", ".lake", "node_modules", "target", "build", "dist"})
ADMIT_PATTERN = re.compile(r"\b(?:sorry|admit)\b")
MAX_SOURCE_BYTES = 1_000_000
MAX_CONTEXTS = 128
MAX_CANDIDATES = 200
MAX_RESPONSE_BYTES = 131_072
MAX_PATCH_BYTES = 65_536


class ProposalError(ValueError):
    """An observation or untrusted API response is invalid."""


def validate_endpoint(raw: str) -> str:
    """Require an explicit HTTP endpoint without credentials or redirects."""
    parsed = urlsplit(raw)
    if parsed.scheme not in {"http", "https"} or not parsed.hostname:
        raise ProposalError("invalid_api_endpoint")
    if parsed.username is not None or parsed.password is not None:
        raise ProposalError("credential_in_api_url")
    if parsed.query or parsed.fragment:
        raise ProposalError("unexpected_api_url_components")
    if parsed.scheme == "http" and parsed.hostname not in {"localhost", "127.0.0.1", "::1"}:
        raise ProposalError("nonlocal_plaintext_api_url")
    return raw.rstrip("/") + "/prove"


def discover(root: Path) -> list[dict[str, Any]]:
    """Inventory bounded, non-symlink Lean files with lexical admit markers."""
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ProposalError("repository_root_not_directory")

    candidates: list[dict[str, Any]] = []

    def walk_error(exc: OSError) -> None:
        raise exc

    for directory, child_dirs, names in os.walk(root, followlinks=False, onerror=walk_error):
        child_dirs[:] = sorted(
            name for name in child_dirs
            if name not in SKIP_DIRECTORIES and not (Path(directory) / name).is_symlink()
        )
        for name in sorted(names):
            file = Path(directory) / name
            if not name.endswith(".lean") or file.is_symlink():
                continue
            raw = file.read_bytes()
            if len(raw) > MAX_SOURCE_BYTES:
                raise ProposalError("oversized_lean_source")
            content = raw.decode("utf-8")
            lines = content.splitlines()
            markers = [index for index, line in enumerate(lines) if ADMIT_PATTERN.search(line)]
            if not markers:
                continue
            if len(markers) > MAX_CONTEXTS:
                raise ProposalError("too_many_markers_in_source")
            contexts = [
                {
                    "line_number": index + 1,
                    "statement": lines[index].strip(),
                    "context": "\n".join(lines[max(0, index - 4):index + 5]),
                }
                for index in markers
            ]
            candidates.append({
                "path": file.relative_to(root).as_posix(),
                "source_sha256": hashlib.sha256(raw).hexdigest(),
                "contexts": contexts,
            })
            if len(candidates) > MAX_CANDIDATES:
                raise ProposalError("too_many_lean_candidates")
    return candidates


def _unique_fields(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    obj: dict[str, Any] = {}
    for name, value in pairs:
        if name in obj:
            raise ProposalError("duplicate_api_json_field")
        obj[name] = value
    return obj


def _invalid_constant(value: str) -> None:
    raise ProposalError("nonfinite_api_json_number")


def fetch_proposal(url: str, candidate: dict[str, Any]) -> str:
    """Return only a digest of a bounded untrusted proposal, never its source."""
    payload = {
        "file_path": candidate["path"],
        "contexts": candidate["contexts"],
    }
    try:
        with requests.post(
            url, json=payload, timeout=(5, 30), allow_redirects=False, stream=True
        ) as response:
            if response.status_code != 200:
                raise ProposalError("api_http_" + str(response.status_code))
            if "application/json" not in response.headers.get("Content-Type", "").lower():
                raise ProposalError("unexpected_api_content_type")
            chunks: list[bytes] = []
            size = 0
            for chunk in response.iter_content(chunk_size=8192):
                size += len(chunk)
                if size > MAX_RESPONSE_BYTES:
                    raise ProposalError("oversized_api_response")
                chunks.append(chunk)
    except requests.RequestException as exc:
        raise ProposalError("api_transport_failure") from exc
    try:
        result = json.loads(
            b"".join(chunks).decode("utf-8"),
            object_pairs_hook=_unique_fields,
            parse_constant=_invalid_constant,
        )
    except (ValueError, UnicodeError) as exc:
        raise ProposalError("invalid_api_json") from exc
    if not isinstance(result, dict):
        raise ProposalError("api_json_not_object")
    patch = result.get("proof_patch")
    if not isinstance(patch, str) or not patch.strip():
        raise ProposalError("missing_proof_patch")
    encoded = patch.encode("utf-8")
    if len(encoded) > MAX_PATCH_BYTES:
        raise ProposalError("oversized_proof_patch")
    return hashlib.sha256(encoded).hexdigest()


def inspect(
    root: Path, *, api_url: str | None, dry_run: bool = False
) -> tuple[dict[str, Any], int]:
    """Collect an inventory and optional proposal digests without modifying source."""
    root = root.resolve(strict=True)
    endpoint = None if dry_run else validate_endpoint(api_url or "")
    candidates = discover(root)
    records: list[dict[str, Any]] = []
    failed = False

    for item in candidates:
        path = root / item["path"]
        record = {
            "path": item["path"],
            "source_sha256": item["source_sha256"],
            "markers": len(item["contexts"]),
            "proposal_verified": False,
        }
        if not dry_run:
            try:
                record["proposal_sha256"] = fetch_proposal(endpoint, item)
                if hashlib.sha256(path.read_bytes()).hexdigest() != item["source_sha256"]:
                    raise ProposalError("source_changed_during_inspection")
                record["status"] = "UNVERIFIED_PROPOSAL"
            except (ProposalError, OSError) as exc:
                record.pop("proposal_sha256", None)
                record["status"] = "FAILED"
                record["error_code"] = str(exc) if isinstance(exc, ProposalError) else "source_read_failure"
                failed = True
        else:
            record["status"] = "LEXICAL_MARKER_ONLY"
        records.append(record)

    status = (
        "INCOMPLETE" if failed
        else "INVENTORY_ONLY" if dry_run
        else "NO_CANDIDATES" if not records
        else "UNVERIFIED_PROPOSALS"
    )
    return {
        "schema_version": 1,
        "evidence_classification": "READ_ONLY_UNVERIFIED",
        "proofs_verified": False,
        "repository_sha": os.environ.get("GITHUB_SHA"),
        "status": status,
        "candidate_count": len(records),
        "records": records,
    }, int(failed)


def write_report(report: dict[str, Any], path: Path, root: Path) -> None:
    """Publish a bounded report outside the repository using an atomic replacement."""
    path = path.resolve()
    if path.is_relative_to(root.resolve()):
        raise ProposalError("report_path_inside_repository")
    path.parent.mkdir(parents=True, exist_ok=True)
    content = (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
    descriptor, temporary = tempfile.mkstemp(prefix=".apollo-report-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--api-url")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--dry-run", action="store_true", help="offline lexical inventory")
    args = parser.parse_args(argv)

    try:
        report, exit_code = inspect(args.root, api_url=args.api_url, dry_run=args.dry_run)
        write_report(report, args.report, args.root)
    except (OSError, UnicodeError, ProposalError, ValueError) as exc:
        print("APOLLO inspection failed: " + str(exc), file=sys.stderr)
        return 1

    print(
        "APOLLO read-only inspection: "
        + report["status"]
        + f"; candidates={report['candidate_count']}; proofs_verified=false"
    )
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
