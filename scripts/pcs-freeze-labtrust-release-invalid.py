#!/usr/bin/env python3
"""Derive labtrust-release negative fixtures from science_claim_bundle.certified.json."""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path

ZERO_COMMIT = "0000000000000000000000000000000000000000"


def write(path: Path, obj: dict) -> None:
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def main() -> int:
    release = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("tests/pcs/fixtures/labtrust-release")
    certified_path = release / "science_claim_bundle.certified.json"
    base = json.loads(certified_path.read_text(encoding="utf-8"))

    # Legacy singular runtime_receipt
    legacy_rr = copy.deepcopy(base)
    rr = legacy_rr.pop("runtime_receipts")
    legacy_rr["runtime_receipt"] = rr[0] if isinstance(rr, list) else rr
    write(release / "invalid_singular_runtime_receipt_bundle.json", legacy_rr)

    # Legacy singular trace_certificate (top-level certificates array -> trace_certificate)
    legacy_tc = copy.deepcopy(base)
    certs = legacy_tc.pop("certificates")
    legacy_tc["trace_certificate"] = certs[0] if isinstance(certs, list) else certs
    write(release / "invalid_trace_certificate_singular_bundle.json", legacy_tc)

    # trace_hash mismatch on certificate
    mismatch = copy.deepcopy(base)
    mismatch["certificates"][0]["trace_hash"] = "sha256:" + "a" * 64
    write(release / "invalid_mismatched_trace_hash.json", mismatch)

    # missing signature_or_digest on claim
    missing_sig = copy.deepcopy(base)
    missing_sig["claim_artifact"].pop("signature_or_digest", None)
    write(release / "invalid_missing_signature_or_digest.json", missing_sig)

    # zero source_commit on bundle (release mode)
    zero_commit = copy.deepcopy(base)
    zero_commit["source_commit"] = ZERO_COMMIT
    write(release / "invalid_zero_source_commit_release.json", zero_commit)

    # Rejected certificate
    rejected = copy.deepcopy(base)
    rejected["certificates"][0]["status"] = "Rejected"
    write(release / "invalid_rejected_certificate.json", rejected)

    # Stale claim artifact
    stale = copy.deepcopy(base)
    stale["claim_artifact"]["status"] = "Stale"
    write(release / "invalid_stale_artifact.json", stale)

    print(f"OK: wrote 7 invalid fixtures under {release}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
