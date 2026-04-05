#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Per-instance debug bundle: copy evidence + eval logs + traces for a list of
# instance IDs into out_dir/<instance_id>/{baseline,pf,eval/} for inspection.

import argparse
import shutil
from pathlib import Path


def _sanitize_instance_id(instance_id: str) -> str:
    """Match bench/swebench util: directory name is alnum, hyphen, underscore."""
    return "".join(c if c.isalnum() or c in "-_" else "_" for c in instance_id)


NEEDED_FILES = [
    "model.patch",
    "metadata.json",
    "run.log",
    "engine_trace.json",
    "cost_report.json",
    "policy_compliance_summary.json",
    "events.jsonl",
]


def safe_copy(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, dst)


def copy_tree_if_exists(src: Path, dst: Path) -> None:
    if not src.exists():
        return
    if src.is_file():
        safe_copy(src, dst)
    else:
        if dst.exists():
            shutil.rmtree(dst)
        shutil.copytree(src, dst)


def find_instance_artifacts(eval_dir: Path, instance_id: str) -> list[Path]:
    """Return any path under eval_dir that contains instance_id in its path."""
    hits = []
    if not eval_dir.exists():
        return hits
    for p in eval_dir.rglob("*"):
        if instance_id in str(p):
            hits.append(p)
    return hits


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Extract per-instance debug bundles (evidence + eval logs + traces) for given instance IDs.",
    )
    ap.add_argument("--instance-ids-file", required=True, help="One instance_id per line (e.g. from list_delta_cases.py)")
    ap.add_argument("--baseline-run-dir", required=True, help="Baseline run dir (runs/.../baseline/<run_id>)")
    ap.add_argument("--pf-run-dir", required=True, help="PF run dir (runs/.../pf/<run_id>)")
    ap.add_argument("--baseline-eval-dir", required=True, help="Baseline harness eval dir (e.g. .../baseline/eval)")
    ap.add_argument("--pf-eval-dir", required=True, help="PF harness eval dir (e.g. .../pf/eval)")
    ap.add_argument("--out-dir", required=True, help="Output root (e.g. .../analysis/cases)")
    args = ap.parse_args()

    ids = [
        line.strip()
        for line in Path(args.instance_ids_file).read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    if not ids:
        print("No instance IDs in file; no regression slice to extract (no-op).", file=__import__("sys").stderr)
        return
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    b_run = Path(args.baseline_run_dir)
    p_run = Path(args.pf_run_dir)
    b_eval = Path(args.baseline_eval_dir)
    p_eval = Path(args.pf_eval_dir)

    for iid in ids:
        case_dir = out_dir / iid
        if case_dir.exists():
            shutil.rmtree(case_dir)
        (case_dir / "baseline").mkdir(parents=True, exist_ok=True)
        (case_dir / "pf").mkdir(parents=True, exist_ok=True)
        (case_dir / "eval").mkdir(parents=True, exist_ok=True)

        # Evidence dirs: run dir uses sanitized instance_id as subdir name
        san = _sanitize_instance_id(iid)
        b_evd = b_run / san
        p_evd = p_run / san

        # Copy known important files if present (and any evidence subdirs)
        for name in NEEDED_FILES:
            for src_root, dst_root in [(b_evd, case_dir / "baseline"), (p_evd, case_dir / "pf")]:
                src = src_root / name
                if src.exists():
                    safe_copy(src, dst_root / name)

        # Copy common evidence directories if present (events.jsonl often under evidence/)
        for dname in ["evidence", "guard", "replay", "proofs"]:
            copy_tree_if_exists(b_evd / dname, case_dir / "baseline" / dname)
            copy_tree_if_exists(p_evd / dname, case_dir / "pf" / dname)

        # Copy any eval artifacts that mention the instance_id
        for hit in find_instance_artifacts(b_eval, iid):
            rel = hit.relative_to(b_eval)
            dst = case_dir / "eval" / "baseline" / rel
            if hit.is_dir():
                copy_tree_if_exists(hit, dst)
            else:
                safe_copy(hit, dst)

        for hit in find_instance_artifacts(p_eval, iid):
            rel = hit.relative_to(p_eval)
            dst = case_dir / "eval" / "pf" / rel
            if hit.is_dir():
                copy_tree_if_exists(hit, dst)
            else:
                safe_copy(hit, dst)

        print(f"Bundled {iid} -> {case_dir}")


if __name__ == "__main__":
    main()
