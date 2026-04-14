#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Post-run validation for SWE-bench predictions.jsonl (and optional predictions.pfmeta.jsonl).
# Checks: line count, instance_id uniqueness and allowed set, non-empty diff in model_patch, pfmeta 1:1 alignment.

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def is_like_diff(text: str) -> bool:
    """True if text looks like a patch (contains diff header or hunk markers)."""
    if not text or not text.strip():
        return False
    t = text.strip()
    return "diff --git" in t or "--- " in t or t.startswith("---") or "\n@@ " in t


def validate(
    predictions_path: Path,
    expected_count: int,
    instance_ids_file: Path | None,
    check_pfmeta: bool = True,
    require_non_empty_diff: bool = True,
) -> tuple[bool, list[str]]:
    """
    Validate predictions.jsonl (and pfmeta if present). Returns (ok, list of error messages).
    """
    errors: list[str] = []
    pred_path = Path(predictions_path)
    if not pred_path.exists():
        return False, [f"Predictions file not found: {pred_path}"]

    allowed_ids: set[str] | None = None
    if instance_ids_file and instance_ids_file.exists():
        allowed_ids = {s.strip() for s in instance_ids_file.read_text(encoding="utf-8").splitlines() if s.strip()}

    lines = [s for s in pred_path.read_text(encoding="utf-8").splitlines() if s.strip()]
    if len(lines) != expected_count:
        errors.append(f"JSONL line count: got {len(lines)}, expected {expected_count}")

    seen: set[str] = set()
    for i, line in enumerate(lines):
        try:
            obj = json.loads(line)
        except json.JSONDecodeError as e:
            errors.append(f"Line {i + 1}: invalid JSON: {e}")
            continue
        iid = obj.get("instance_id")
        if not iid:
            errors.append(f"Line {i + 1}: missing instance_id")
            continue
        if iid in seen:
            errors.append(f"instance_id appears more than once: {iid}")
        seen.add(iid)
        if allowed_ids is not None and iid not in allowed_ids:
            errors.append(f"instance_id not in allowed set: {iid}")
        if require_non_empty_diff:
            patch = obj.get("model_patch") or ""
            if not is_like_diff(patch):
                errors.append(f"Line {i + 1} ({iid}): model_patch is empty or not a diff")

    pfmeta_path = pred_path.parent / (pred_path.stem + ".pfmeta.jsonl")
    if check_pfmeta and pfmeta_path.exists():
        pfmeta_lines = [s for s in pfmeta_path.read_text(encoding="utf-8").splitlines() if s.strip()]
        if len(pfmeta_lines) != len(lines):
            errors.append(
                f"predictions.pfmeta.jsonl line count ({len(pfmeta_lines)}) != predictions.jsonl ({len(lines)})"
            )
        else:
            for i, line in enumerate(pfmeta_lines):
                try:
                    rec = json.loads(line)
                    meta_iid = rec.get("instance_id")
                    pred_iid = json.loads(lines[i]).get("instance_id") if i < len(lines) else None
                    if meta_iid != pred_iid:
                        errors.append(f"pfmeta line {i + 1}: instance_id mismatch (pfmeta={meta_iid!r}, pred={pred_iid!r})")
                except json.JSONDecodeError as e:
                    errors.append(f"pfmeta line {i + 1}: invalid JSON: {e}")
    elif check_pfmeta and not pfmeta_path.exists():
        pass  # pfmeta optional; only validate alignment when present

    return len(errors) == 0, errors


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate SWE-bench predictions.jsonl (and pfmeta) after a run.")
    parser.add_argument("predictions", type=Path, help="Path to predictions.jsonl")
    parser.add_argument(
        "-n",
        "--expected-count",
        type=int,
        default=20,
        help="Expected number of lines (default: 20)",
    )
    parser.add_argument(
        "--instance-ids-file",
        type=Path,
        default=None,
        help="Optional file with one instance_id per line (each must appear exactly once)",
    )
    parser.add_argument(
        "--no-pfmeta",
        action="store_true",
        help="Skip pfmeta alignment check even if file exists",
    )
    parser.add_argument(
        "--allow-empty-patch",
        action="store_true",
        help="Do not require model_patch to be a non-empty diff (e.g. when OpenHands not installed)",
    )
    parser.add_argument(
        "--allow-partial",
        action="store_true",
        help="Allow validating when run_status.json indicates partial or failed run (default: fail unless status is complete)",
    )
    args = parser.parse_args()

    run_status_path = args.predictions.parent / "run_status.json"
    if run_status_path.exists():
        try:
            run_status = json.loads(run_status_path.read_text(encoding="utf-8"))
            if run_status.get("status") != "complete" and not args.allow_partial:
                print(
                    f"Run status is {run_status.get('status', 'unknown')}; use --allow-partial to validate anyway.",
                    file=sys.stderr,
                )
                return 1
        except (json.JSONDecodeError, OSError):
            pass

    ok, errs = validate(
        args.predictions,
        expected_count=args.expected_count,
        instance_ids_file=args.instance_ids_file,
        check_pfmeta=not args.no_pfmeta,
        require_non_empty_diff=not args.allow_empty_patch,
    )
    if ok:
        print("Validation passed.", file=sys.stderr)
        return 0
    for e in errs:
        print(e, file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
