#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Run SWE-bench harness evaluation for both baseline and PF-guarded predictions.
# Uses the same harness command for both; outputs go to separate eval dirs.
# Resolves dataset ID by trying candidates in order and writes the chosen ID to
# experiment_dir/harness_dataset_id.txt to avoid future ambiguity.
# Requires: pip install swebench (or SWE-bench from source), Docker for local eval.

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

# Try in order; first that loads (via datasets) is used and recorded.
CANDIDATE_DATASET_IDS = [
    "SWE-bench/SWE-bench_Lite",
    "princeton-nlp/SWE-bench_Lite",
]


def count_nonempty_prediction_patches(predictions_path: Path) -> tuple[int, int]:
    """
    Return (nonempty_patch_rows, total_jsonl_rows) for a SWE-bench predictions.jsonl.
    Harness skips Docker eval for rows with empty model_patch/patch, which yields 'No instances to run.'
    """
    total = 0
    nonempty = 0
    try:
        text = predictions_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0, 0
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        total += 1
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        mp = obj.get("model_patch")
        if mp is None:
            mp = obj.get("patch")
        if isinstance(mp, str) and mp.strip():
            nonempty += 1
    return nonempty, total


def docker_rm_stale_eval_containers(run_id: str) -> None:
    """
    Remove SWE-bench harness eval containers for a specific run_id only.

    Containers are expected to match the pattern ``sweb.eval.<instance_id>.<run_id>``
    (``run_id`` is the final dot-separated segment). This avoids broad ``name=<run_id>``
    matches that could remove unrelated containers.
    """
    rid = (run_id or "").strip()
    if not rid:
        return
    try:
        proc = subprocess.run(
            ["docker", "ps", "-a", "--filter", "name=sweb.eval", "--format", "{{.ID}}\t{{.Names}}"],
            capture_output=True,
            text=True,
            timeout=120,
        )
        if proc.returncode != 0:
            sys.stderr.write(
                "Warning: docker ps for stale eval containers failed: %s\n"
                % ((proc.stderr or "").strip() or "unknown")
            )
            return
        to_remove: list[str] = []
        for line in (proc.stdout or "").splitlines():
            line = line.strip()
            if not line or "\t" not in line:
                continue
            cid, name = line.split("\t", 1)
            cid = cid.strip()
            name = name.strip()
            if "sweb.eval" not in name:
                continue
            last = name.rsplit(".", 1)[-1] if "." in name else ""
            if last == rid:
                to_remove.append(cid)
        for cid in to_remove:
            r = subprocess.run(
                ["docker", "rm", "-f", cid],
                capture_output=True,
                text=True,
                timeout=120,
            )
            if r.returncode == 0:
                print("Removed stale eval container %s (run_id suffix match %s)" % (cid, rid))
            else:
                sys.stderr.write(
                    "Warning: docker rm -f %s failed: %s\n"
                    % (cid, (r.stderr or "").strip() or "unknown")
                )
    except FileNotFoundError:
        sys.stderr.write("Warning: docker not on PATH; skip stale container cleanup\n")
    except subprocess.TimeoutExpired:
        sys.stderr.write("Warning: docker cleanup timed out\n")


def resolve_dataset_id(split: str) -> str | None:
    """Try each candidate dataset ID; return the first that loads successfully, or None."""
    try:
        import datasets
    except ImportError:
        return CANDIDATE_DATASET_IDS[0]
    for candidate in CANDIDATE_DATASET_IDS:
        try:
            datasets.load_dataset(candidate, split=split)
            return candidate
        except Exception:
            continue
    return None


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run SWE-bench harness evaluation for baseline and PF predictions (same command for both).",
    )
    parser.add_argument(
        "--baseline-predictions",
        type=str,
        default="runs/exp-step2-lite-smoke/baseline/predictions.jsonl",
        help="Path to baseline predictions.jsonl",
    )
    parser.add_argument(
        "--pf-predictions",
        type=str,
        default="runs/exp-step2-lite-smoke/pf/predictions.jsonl",
        help="Path to PF-guarded predictions.jsonl",
    )
    parser.add_argument(
        "--baseline-eval-dir",
        type=str,
        default="runs/exp-step2-lite-smoke/baseline/eval",
        help="Output directory for baseline eval (run report and logs)",
    )
    parser.add_argument(
        "--pf-eval-dir",
        type=str,
        default="runs/exp-step2-lite-smoke/pf/eval",
        help="Output directory for PF eval (run report and logs)",
    )
    parser.add_argument(
        "--experiment-dir",
        type=str,
        default="runs/exp-step2-lite-smoke",
        help="Experiment directory; chosen dataset ID is written to <experiment_dir>/harness_dataset_id.txt",
    )
    parser.add_argument(
        "--dataset",
        type=str,
        default="auto",
        help="Dataset ID (default: auto = try SWE-bench/SWE-bench_Lite then princeton-nlp/SWE-bench_Lite); recorded to harness_dataset_id.txt",
    )
    parser.add_argument(
        "--split",
        type=str,
        default="test",
        help="Dataset split",
    )
    parser.add_argument(
        "--run-baseline-only",
        action="store_true",
        help="Only run baseline evaluation",
    )
    parser.add_argument(
        "--run-pf-only",
        action="store_true",
        help="Only run PF evaluation",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1800,
        help="Timeout in seconds per instance (default 1800)",
    )
    parser.add_argument(
        "--max-workers",
        type=int,
        default=4,
        help="Max parallel workers for harness (default 4). On stressed WSL/Docker hosts try 1 or 2 if you see many harness errors (e.g. accept4 failed 110).",
    )
    parser.add_argument(
        "--rm-stale-eval-containers",
        action="store_true",
        help=(
            "Before each harness invocation, docker rm -f containers whose names match the "
            "run_id (fixes 409 'container name already in use' after a crashed eval)."
        ),
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent.parent
    baseline_pred = Path(args.baseline_predictions)
    pf_pred = Path(args.pf_predictions)
    baseline_dir = Path(args.baseline_eval_dir)
    pf_dir = Path(args.pf_eval_dir)
    experiment_dir = Path(args.experiment_dir)

    if args.dataset == "auto":
        dataset_id = resolve_dataset_id(args.split)
        if dataset_id is None:
            print(
                "Error: none of the candidate dataset IDs could be loaded: %s"
                % CANDIDATE_DATASET_IDS,
                file=sys.stderr,
            )
            return 1
        print("Using dataset: %s" % dataset_id)
    else:
        dataset_id = args.dataset

    experiment_dir.mkdir(parents=True, exist_ok=True)
    harness_dataset_id_file = experiment_dir / "harness_dataset_id.txt"
    harness_dataset_id_file.write_text(dataset_id.strip() + "\n", encoding="utf-8")
    print("Recorded dataset ID to %s" % harness_dataset_id_file)

    def _run_id_from_predictions_dir(pred_path: Path) -> str:
        """Read run_id from run_status.json next to predictions file; fallback to dir label."""
        status_path = pred_path.parent / "run_status.json"
        if status_path.exists():
            try:
                data = json.loads(status_path.read_text(encoding="utf-8"))
                rid = data.get("run_id")
                if rid:
                    return str(rid)
            except (json.JSONDecodeError, OSError):
                pass
        return "baseline" if "baseline" in str(pred_path) else "pf"

    def _predictions_sha256(pred_path: Path) -> str | None:
        """Read predictions.sha256 from same dir as predictions file if present."""
        sha_path = pred_path.parent / "predictions.sha256"
        if sha_path.exists():
            try:
                return sha_path.read_text(encoding="utf-8").strip()
            except OSError:
                pass
        return None

    def run_harness(predictions_path: Path, output_dir: Path, run_id: str) -> int:
        if not predictions_path.exists():
            print(f"Predictions file not found: {predictions_path}", file=sys.stderr)
            return 1
        ne, nt = count_nonempty_prediction_patches(predictions_path)
        if nt > 0 and ne == 0:
            print(
                "Warning: %s has %d prediction row(s) but none have a non-empty model_patch/patch. "
                "SWE-bench harness will print 'No instances to run.' and skip Docker eval for this file."
                % (predictions_path, nt),
                file=sys.stderr,
            )
        output_dir.mkdir(parents=True, exist_ok=True)
        cmd = [
            sys.executable,
            "-m",
            "swebench.harness.run_evaluation",
            "--predictions_path", str(predictions_path.resolve()),
            "--dataset_name", dataset_id,
            "--split", args.split,
            "--run_id", run_id,
            "--report_dir", str(output_dir.resolve()),
            "--timeout", str(args.timeout),
            "--max_workers", str(args.max_workers),
        ]
        max_attempts = 2
        result = None
        for attempt in range(1, max_attempts + 1):
            if attempt > 1:
                print(
                    "Harness exited non-zero. Retrying once (transient Docker errors are common).",
                    file=sys.stderr,
                )
            print(f"Running: {' '.join(cmd)}")
            print(f"  cwd={output_dir}")
            result = subprocess.run(
                cmd,
                cwd=str(output_dir),
                env={**__import__("os").environ},
            )
            if result.returncode == 0:
                break
        if result.returncode != 0:
            print(
                "Docker failed. If you see '500 Server Error' for /version, Docker is not reachable from WSL: "
                "start Docker Desktop, ensure WSL 2 integration is enabled, then re-run. "
                "If the failure was during image cleanup (images/json), restart Docker Desktop and re-run Phase 4.1.",
                file=sys.stderr,
            )
            return result.returncode
        eval_meta = {
            "run_id": run_id,
            "predictions_sha256": _predictions_sha256(predictions_path),
            "dataset_name": dataset_id,
            "split": args.split,
            "harness_dataset_id": dataset_id,
        }
        try:
            import datasets
            eval_meta["datasets_version"] = getattr(datasets, "__version__", "unknown")
        except ImportError:
            eval_meta["datasets_version"] = None
        try:
            import swebench
            eval_meta["swebench_version"] = getattr(swebench, "__version__", "unknown")
        except ImportError:
            eval_meta["swebench_version"] = None
        (output_dir / "eval_metadata.json").write_text(
            json.dumps(eval_meta, indent=2),
            encoding="utf-8",
        )
        return 0

    ran = False
    if not args.run_pf_only:
        ran = True
        baseline_run_id = _run_id_from_predictions_dir(baseline_pred)
        if args.rm_stale_eval_containers:
            docker_rm_stale_eval_containers(baseline_run_id)
        if run_harness(baseline_pred, baseline_dir, baseline_run_id) != 0:
            return 1
    if not args.run_baseline_only:
        ran = True
        pf_run_id = _run_id_from_predictions_dir(pf_pred)
        if args.rm_stale_eval_containers:
            docker_rm_stale_eval_containers(pf_run_id)
        if run_harness(pf_pred, pf_dir, pf_run_id) != 0:
            return 1
    if not ran:
        print("Run at least one of baseline or PF (omit --run-baseline-only and --run-pf-only for both).", file=sys.stderr)
        return 2

    print("Eval runs finished. Collect results with:")
    print(f"  python experiments/scripts/collect_eval_results.py {baseline_dir} {pf_dir}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
