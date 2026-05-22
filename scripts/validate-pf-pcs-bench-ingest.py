#!/usr/bin/env python3
"""Validate a PF-produced PcsBenchIngest.v0 against pcs-core (schema, semantics, sidecars, adequacy)."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def _resolve_pcs_core_python(pcs_core: Path | None) -> Path:
    root = pcs_core
    if root is None:
        env = __import__("os").environ.get("PCS_CORE_PATH", "").strip()
        if env:
            root = Path(env)
        else:
            here = Path(__file__).resolve().parents[1]
            sibling = here.parent / "pcs-core"
            if (sibling / "python" / "pcs_core").is_dir():
                root = sibling
    if root is None or not (root / "python" / "pcs_core").is_dir():
        print(
            "PCS_CORE_PATH or ../pcs-core/python is required",
            file=sys.stderr,
        )
        sys.exit(2)
    py_root = root / "python"
    sys.path.insert(0, str(py_root))
    return py_root


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--ingest",
        type=Path,
        required=True,
        help="Path to pcs_bench_ingest.v0.json",
    )
    parser.add_argument(
        "--bundle-dir",
        type=Path,
        default=None,
        help="Benchmark bundle root (defaults to parent of --ingest)",
    )
    parser.add_argument(
        "--pcs-core",
        type=Path,
        default=None,
        help="pcs-core repo root (default: PCS_CORE_PATH or ../pcs-core)",
    )
    parser.add_argument(
        "--release-grade",
        action="store_true",
        help="Require release-grade or external-review-grade adequacy",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON report")
    args = parser.parse_args()

    ingest_path = args.ingest.resolve()
    if not ingest_path.is_file():
        print(f"missing ingest: {ingest_path}", file=sys.stderr)
        return 1

    bundle_dir = (args.bundle_dir or ingest_path.parent).resolve()

    _resolve_pcs_core_python(args.pcs_core)

    from pcs_core.benchmark_ingest import (  # noqa: E402
        assess_ingest_adequacy_tier,
        validate_benchmark_ingest_file,
    )

    errors = list(validate_benchmark_ingest_file(ingest_path, check_release_grade=args.release_grade))

    ingest = json.loads(ingest_path.read_text(encoding="utf-8"))
    for index, ref in enumerate(ingest.get("artifact_refs") or []):
        if not isinstance(ref, dict):
            errors.append(f"artifact_refs[{index}] must be an object")
            continue
        rel = ref.get("path")
        if not isinstance(rel, str) or not rel.strip():
            errors.append(f"artifact_refs[{index}] missing path")
            continue
        sidecar = bundle_dir / Path(rel.replace("\\", "/"))
        if not sidecar.is_file():
            errors.append(f"artifact_refs[{index}] missing sidecar {sidecar.relative_to(bundle_dir).as_posix()}")

    tier, findings = assess_ingest_adequacy_tier(ingest)

    if args.json:
        print(
            json.dumps(
                {
                    "status": "failed" if errors else "passed",
                    "ingest": str(ingest_path),
                    "bundle_dir": str(bundle_dir),
                    "adequacy_tier": tier,
                    "adequacy_findings": findings,
                    "errors": errors,
                },
                indent=2,
            ),
        )
        return 1 if errors else 0

    if errors:
        for err in errors:
            print(f"FAIL {err}", file=sys.stderr)
        return 1

    print(f"OK {ingest_path.name} adequacy={tier}")
    for item in findings:
        print(f"  note: {item}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
