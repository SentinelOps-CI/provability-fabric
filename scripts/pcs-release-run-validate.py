#!/usr/bin/env python3
"""Validate PF release-run artifacts against the certified bundle handoff."""
from __future__ import annotations

import json
import sys
from pathlib import Path


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: pcs-release-run-validate.py <release-run-dir>", file=sys.stderr)
        return 2
    run = Path(sys.argv[1])
    certified = load_json(run / "science_claim_bundle.certified.json")
    vr = load_json(run / "verification_result.json")
    signed = load_json(run / "signed_science_claim_bundle.json")

    cert_id = certified["certificates"][0]["certificate_id"]
    vr_cert = None
    for check in vr.get("checks", []):
        if check.get("check_id") == "evidence_refs_complete":
            refs = check.get("details", {}).get("certificate_refs") or []
            if refs:
                vr_cert = refs[0]
            break
    if vr.get("verified_input"):
        vr_cert = vr_cert or vr["verified_input"].get("certificate_id")
    signed_cert = signed["science_claim_bundle"]["certificates"][0]["certificate_id"]

    if cert_id != vr_cert or cert_id != signed_cert:
        print(
            f"certificate_id mismatch: bundle={cert_id!r} vr={vr_cert!r} signed={signed_cert!r}",
            file=sys.stderr,
        )
        return 1

    vi = vr.get("verified_input") or {}
    for key in ("bundle_hash", "certificate_id", "trace_hash"):
        if not vi.get(key):
            print(f"verification_result.verified_input missing {key}", file=sys.stderr)
            return 1
    if vi.get("certificate_id") != cert_id:
        print("verified_input.certificate_id mismatch", file=sys.stderr)
        return 1

    signed_hash = signed.get("signed_input_bundle_hash")
    if signed_hash and signed_hash != vi.get("bundle_hash"):
        print("signed_input_bundle_hash != verified_input.bundle_hash", file=sys.stderr)
        return 1

    pf_commit = vr.get("source_commit", "")
    forbidden = {
        "0000000000000000000000000000000000000000",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
        "cccccccccccccccccccccccccccccccccccccccc",
        "dddddddddddddddddddddddddddddddddddddddd",
        "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee",
    }
    if pf_commit in forbidden or signed.get("source_commit") in forbidden:
        print("PF placeholder source_commit detected", file=sys.stderr)
        return 1

    print(f"OK: release-run PF chain aligned on {cert_id}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
