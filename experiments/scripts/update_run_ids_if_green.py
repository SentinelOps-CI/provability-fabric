#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Update run-ids.md only when all gates pass: validate_predictions (baseline + PF),
# check_no_stub, validate_pf_run, compare_runs with --require-harness --require-compliance
# --require-patch-apply --require-priced-models.

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
from experiments.scripts.publish_docs import (  # noqa: E402
    build_publish_md,
    build_results_md,
    build_verify_md,
)
from experiments.scripts.publish_manifest import (  # noqa: E402
    maybe_gpg_detach_sign_manifest,
    write_publish_manifest_sha256,
)


def _git_head() -> str:
    """Return current git commit (short) or empty string."""
    try:
        r = subprocess.run(
            ["git", "rev-parse", "--short=12", "HEAD"],
            cwd=str(_REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=5,
        )
        return (r.stdout or "").strip() if r.returncode == 0 else ""
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return ""


def _run(cmd: list[str], desc: str) -> bool:
    proc = subprocess.run(cmd, cwd=str(_REPO_ROOT), capture_output=True, text=True)
    if proc.returncode != 0:
        print("FAILED: %s" % desc, file=sys.stderr)
        if proc.stderr:
            print(proc.stderr, file=sys.stderr)
        return False
    return True


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Update run-ids.md in experiment dir only when all gates pass.",
    )
    parser.add_argument("--experiment-dir", type=Path, required=True, help="Experiment dir (e.g. experiments/exp-step2-lite-smoke)")
    parser.add_argument("--baseline-run-dir", type=Path, required=True, help="Baseline run dir (e.g. runs/exp-step2-lite-smoke/baseline/<run_id>)")
    parser.add_argument("--pf-run-dir", type=Path, required=True, help="PF run dir (e.g. runs/exp-step2-lite-smoke/pf/<run_id>)")
    parser.add_argument("--instance-ids-file", type=Path, default=None, help="Instance IDs file for validate_predictions -n count")
    parser.add_argument("--expected-count", type=int, default=None, help="Expected prediction count; if unset, script infers from instance-ids-file lines")
    parser.add_argument("--allow-empty-patch", action="store_true", help="Pass --allow-empty-patch to validate_predictions (allow runs where some instances produced no diff)")
    args = parser.parse_args()

    exp_dir = args.experiment_dir.resolve()
    baseline_run = args.baseline_run_dir.resolve()
    pf_run = args.pf_run_dir.resolve()

    baseline_root = baseline_run.parent
    pf_root = pf_run.parent
    baseline_pred = baseline_root / "predictions.jsonl"
    pf_pred = pf_root / "predictions.jsonl"

    if not baseline_pred.exists():
        print("Error: baseline predictions not found: %s" % baseline_pred, file=sys.stderr)
        return 1
    if not pf_pred.exists():
        print("Error: PF predictions not found: %s" % pf_pred, file=sys.stderr)
        return 1

    n_flag = []
    if args.expected_count is not None:
        n_flag = ["-n", str(args.expected_count)]
    elif args.instance_ids_file and args.instance_ids_file.exists():
        n = len([s for s in args.instance_ids_file.read_text(encoding="utf-8").splitlines() if s.strip()])
        n_flag = ["-n", str(n)]
    else:
        n_flag = ["-n", "20"]

    id_file_flag = []
    if args.instance_ids_file and args.instance_ids_file.exists():
        id_file_flag = ["--instance-ids-file", str(args.instance_ids_file)]

    if not _run(
        [sys.executable, str(_SCRIPT_DIR / "validate_predictions.py"), str(baseline_pred)] + n_flag + id_file_flag + (["--allow-empty-patch"] if args.allow_empty_patch else []),
        "validate_predictions (baseline)",
    ):
        return 1
    if not _run(
        [sys.executable, str(_SCRIPT_DIR / "validate_predictions.py"), str(pf_pred)] + n_flag + id_file_flag + (["--allow-empty-patch"] if args.allow_empty_patch else []),
        "validate_predictions (PF)",
    ):
        return 1
    if not _run(
        [sys.executable, str(_SCRIPT_DIR / "check_no_stub.py"), str(baseline_root), str(pf_root)],
        "check_no_stub",
    ):
        return 1
    if not _run(
        [sys.executable, str(_REPO_ROOT / "bench" / "swebench" / "validate_pf_run.py"), str(pf_run)],
        "validate_pf_run",
    ):
        return 1
    runs_root = baseline_root.parent
    if not _run(
        [
            sys.executable,
            str(_SCRIPT_DIR / "compare_runs.py"),
            "--experiment-dir", str(runs_root),
            "--out", str(runs_root),
            "--baseline-run-dir", str(baseline_run),
            "--pf-run-dir", str(pf_run),
            "--baseline-eval-dir", str(baseline_root / "eval"),
            "--pf-eval-dir", str(pf_root / "eval"),
            "--require-harness",
            "--require-compliance",
            "--require-patch-apply",
            "--require-priced-models",
        ],
        "compare_runs (gated)",
    ):
        return 1

    baseline_run_id = baseline_run.name
    pf_run_id = pf_run.name
    run_ids_md = exp_dir / "run-ids.md"

    # Compute repo-relative paths so run-ids.md is portable across machines.
    def _rel(p: Path) -> str:
        try:
            return str(p.relative_to(_REPO_ROOT))
        except ValueError:
            return str(p)

    exp_rel = _rel(exp_dir)
    baseline_rel = _rel(baseline_run)
    pf_rel = _rel(pf_run)
    runs_exp_rel = _rel(baseline_root.parent)  # e.g. runs/exp-step2-lite-smoke

    content = """# Recorded run IDs (Case 1.1 / 1.2)

Use these in compare (Case 1.3/1.4) and for `validate_pf_run.py`.

**Canonical way to update:** run `python experiments/scripts/update_run_ids_if_green.py --experiment-dir %(exp)s --baseline-run-dir %(baseline)s --pf-run-dir %(pf)s` and add **`--instance-ids-file`** / **`--expected-count`** as needed. When any instance may have an empty `model_patch` (same as `run-baseline-pf-cycle.sh --update-run-ids`), pass **`--allow-empty-patch`** so baseline and PF `validate_predictions` match Phase 2.2/3.2. This script only writes run-ids.md when all gates pass (validate_predictions, check_no_stub, validate_pf_run, compare_runs with --require-harness --require-compliance --require-patch-apply --require-priced-models). Compare and metrics_full.json are written under `runs/<experiment_id>/`.

| Run   | run_id |
|-------|--------|
| Baseline (Case 1.1) | `%(baseline_id)s` |
| PF-guarded (Case 1.2) | `%(pf_id)s` |

Compare command (same hard gates as the cycle script; replace run IDs if needed):

```bash
python experiments/scripts/compare_runs.py \\
  --experiment-dir %(runs_exp)s \\
  --baseline-run-dir %(runs_exp)s/baseline/%(baseline_id)s \\
  --pf-run-dir %(runs_exp)s/pf/%(pf_id)s \\
  --baseline-eval-dir %(runs_exp)s/baseline/eval \\
  --pf-eval-dir %(runs_exp)s/pf/eval \\
  --require-harness \\
  --require-compliance \\
  --require-patch-apply \\
  --require-priced-models
```
""" % {
        "exp": exp_rel,
        "baseline": baseline_rel,
        "pf": pf_rel,
        "runs_exp": runs_exp_rel,
        "baseline_id": baseline_run_id,
        "pf_id": pf_run_id,
    }
    run_ids_md.write_text(content, encoding="utf-8")
    print("Updated %s with baseline=%s pf=%s" % (run_ids_md, baseline_run_id, pf_run_id))

    # Wire export: produce publish bundle and PUBLISH.md when green
    compare_json = runs_root / "compare.json"
    pf_eval_dir = pf_root / "eval"
    publish_dir = runs_root / "publish"
    if compare_json.exists():
        export_cmd = [
            sys.executable,
            str(_SCRIPT_DIR / "export_publish_artifacts.py"),
            "--pf-predictions", str(pf_pred),
            "--pf-run-dir", str(pf_run),
            "--pf-eval-dir", str(pf_eval_dir),
            "--compare-json", str(compare_json),
            "--out-dir", str(publish_dir),
            "--experiment-id", exp_dir.name,
            "--baseline-run-id", baseline_run_id,
            "--pf-run-id", pf_run_id,
        ]
        if _run(export_cmd, "export_publish_artifacts"):
            try:
                compare_data = json.loads(compare_json.read_text(encoding="utf-8"))
                b = compare_data.get("baseline") or {}
                p = compare_data.get("pf") or {}
                parity_gate = None
                if b.get("solve_rate") is not None and p.get("solve_rate") is not None:
                    parity_gate = bool(p["solve_rate"] >= b["solve_rate"] - 0.01)
                ts = datetime.now(timezone.utc).isoformat()
                git_sha = _git_head()

                (publish_dir / "PUBLISH.md").write_text(
                    "\n".join(build_publish_md(baseline_run_id, pf_run_id, compare_data)),
                    encoding="utf-8",
                )
                print("Wrote %s/PUBLISH.md" % publish_dir)

                # Golden stamp for automation: run IDs, commit, timestamp, parity gate.
                golden_ok = {
                    "baseline_run_id": baseline_run_id,
                    "pf_run_id": pf_run_id,
                    "pf_commit": git_sha,
                    "timestamp_utc": ts,
                    "parity_gate_passed": parity_gate,
                }
                (publish_dir / "GOLDEN.ok").write_text(
                    json.dumps(golden_ok, indent=2), encoding="utf-8"
                )
                print("Wrote %s/GOLDEN.ok" % publish_dir)

                # RESULTS.md: audit-friendly summary (no marketing).
                (publish_dir / "RESULTS.md").write_text(
                    "\n".join(build_results_md(
                        baseline_run_id, pf_run_id, git_sha or "", ts, compare_data, parity_gate
                    )),
                    encoding="utf-8",
                )
                print("Wrote %s/RESULTS.md" % publish_dir)

                # VERIFY.md: reviewer-proof entrypoint (brutally factual, links to generated artifacts only).
                (publish_dir / "VERIFY.md").write_text(
                    "\n".join(build_verify_md(exp_dir.name, publish_dir, compare_json)),
                    encoding="utf-8",
                )
                print("Wrote %s/VERIFY.md" % publish_dir)

                write_publish_manifest_sha256(publish_dir)
                print("Wrote %s/MANIFEST.sha256" % publish_dir)
                maybe_gpg_detach_sign_manifest(publish_dir)

                # Scale Results Ledger: append one row for this green run (cumulative results).
                ledger_cmd = [
                    sys.executable,
                    str(_SCRIPT_DIR / "append_scale_results_ledger.py"),
                    "--compare-json", str(compare_json),
                    "--experiment-id", exp_dir.name,
                    "--pf-commit", (git_sha or ""),
                ]
                stress_summary = runs_root / "stress_summary.json"
                if stress_summary.exists():
                    ledger_cmd += ["--stress-summary", str(stress_summary)]
                _run(ledger_cmd, "append_scale_results_ledger")
            except (json.JSONDecodeError, OSError):
                pass

    return 0


if __name__ == "__main__":
    sys.exit(main())
