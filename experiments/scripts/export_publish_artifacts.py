#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Export a SWE-bench/experiments-style publish directory: metadata.yaml,
# all_preds.jsonl, logs/<instance_id>/ (PF evidence + harness logs), trajs/<instance_id>.json.

import argparse
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

_SCRIPT_DIR = Path(__file__).resolve().parent
_REPO_ROOT = _SCRIPT_DIR.parent.parent
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
from experiments.scripts.publish_bundle import (  # noqa: E402
    EXPORT_PRODUCES_DIRS,
    EXPORT_PRODUCES_FILES,
)


def _sanitize_instance_id(instance_id: str) -> str:
    """Match bench/swebench util: directory name is alnum, hyphen, underscore."""
    return "".join(c if c.isalnum() or c in "-_" else "_" for c in instance_id)


PARITY_TOLERANCE = 0.01  # pf.solve_rate >= baseline.solve_rate - PARITY_TOLERANCE


def main() -> None:
    ap = argparse.ArgumentParser(
        description="Export publishable artifacts (metadata, predictions, logs, trajs) for SWE-bench-style submission.",
    )
    ap.add_argument("--pf-predictions", required=True, help="Path to PF predictions.jsonl")
    ap.add_argument("--pf-run-dir", required=True, help="PF run dir (runs/.../pf/<run_id>)")
    ap.add_argument("--pf-eval-dir", required=True, help="PF harness eval dir (e.g. .../pf/eval)")
    ap.add_argument("--compare-json", required=True, help="Path to compare.json from compare_runs.py")
    ap.add_argument("--out-dir", required=True, help="Output publish root (e.g. runs/.../publish)")
    ap.add_argument("--experiment-id", default="", help="Experiment ID for metadata")
    ap.add_argument("--baseline-run-id", default="", help="Baseline run ID for metadata")
    ap.add_argument("--pf-run-id", default="", help="PF run ID for metadata")
    args = ap.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    pf_run = Path(args.pf_run_dir)
    pf_eval = Path(args.pf_eval_dir)

    # Load compare.json for rates and gate
    compare_path = Path(args.compare_json)
    compare: dict = {}
    if compare_path.exists():
        try:
            compare = json.loads(compare_path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            pass
    baseline_rate = compare.get("baseline") and compare["baseline"].get("solve_rate")
    pf_rate = compare.get("pf") and compare["pf"].get("solve_rate")
    violation_final = (compare.get("pf") or {}).get("policy_violation_rate_final")
    parity_gate_passed = None
    if baseline_rate is not None and pf_rate is not None:
        parity_gate_passed = bool(pf_rate >= baseline_rate - PARITY_TOLERANCE)

    # Instance list from predictions
    pred_path = Path(args.pf_predictions)
    instance_ids: list[str] = []
    pred_lines: list[str] = []
    if pred_path.exists():
        for line in pred_path.read_text(encoding="utf-8").strip().splitlines():
            if not line.strip():
                continue
            pred_lines.append(line)
            try:
                obj = json.loads(line)
                iid = obj.get("instance_id") or obj.get("id")
                if iid:
                    instance_ids.append(iid)
            except json.JSONDecodeError:
                pass

    # all_preds.jsonl
    (out_dir / "all_preds.jsonl").write_text("\n".join(pred_lines) + ("\n" if pred_lines else ""), encoding="utf-8")
    print(f"Wrote {out_dir / 'all_preds.jsonl'} ({len(pred_lines)} lines)")

    # logs/<instance_id>/ from PF run evidence + harness
    logs_dir = out_dir / "logs"
    logs_dir.mkdir(parents=True, exist_ok=True)
    for iid in instance_ids:
        san = _sanitize_instance_id(iid)
        inst_src = pf_run / san
        inst_dst = logs_dir / iid
        if inst_dst.exists():
            shutil.rmtree(inst_dst)
        inst_dst.mkdir(parents=True, exist_ok=True)
        if inst_src.is_dir():
            for item in inst_src.iterdir():
                dst_item = inst_dst / item.name
                if item.is_file():
                    shutil.copy2(item, dst_item)
                else:
                    shutil.copytree(item, dst_item)
        # Harness logs: any file under pf_eval whose path contains instance_id
        if pf_eval.is_dir():
            for hit in pf_eval.rglob("*"):
                if hit.is_file() and iid in hit.as_posix():
                    rel = hit.relative_to(pf_eval)
                    dst = inst_dst / "harness" / rel
                    dst.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(hit, dst)
        print(f"  logs/{iid}/")
    print(f"Wrote {len(instance_ids)} log dirs under {logs_dir}")

    # trajs/<instance_id>.json (engine_trace.json)
    trajs_dir = out_dir / "trajs"
    trajs_dir.mkdir(parents=True, exist_ok=True)
    for iid in instance_ids:
        san = _sanitize_instance_id(iid)
        trace_src = pf_run / san / "engine_trace.json"
        if trace_src.exists():
            trajs_dir.joinpath(f"{iid}.json").write_text(
                trace_src.read_text(encoding="utf-8"), encoding="utf-8"
            )
    print(f"Wrote trajs/ for {sum(1 for iid in instance_ids if (pf_run / _sanitize_instance_id(iid) / 'engine_trace.json').exists())} instances")

    # metadata.yaml
    meta = {
        "experiment_id": args.experiment_id or "exp-step2-lite-smoke",
        "baseline_run_id": args.baseline_run_id,
        "pf_run_id": args.pf_run_id,
        "dataset": "SWE-bench_Lite",
        "split": "test",
        "slice_n": len(instance_ids),
        "baseline_solve_rate": baseline_rate,
        "pf_solve_rate": pf_rate,
        "parity_gate_passed": parity_gate_passed,
        "parity_rule": f"pf.solve_rate >= baseline.solve_rate - {PARITY_TOLERANCE}",
        "pf_policy_violation_rate_final": violation_final,
        "exported_at": datetime.now(timezone.utc).isoformat(),
    }
    yaml_lines = []
    for k, v in meta.items():
        if v is None:
            v = "null"
        elif isinstance(v, bool):
            v = "true" if v else "false"
        elif isinstance(v, float):
            v = str(v)
        yaml_lines.append(f"{k}: {v}")
    (out_dir / "metadata.yaml").write_text("\n".join(yaml_lines) + "\n", encoding="utf-8")
    print(f"Wrote {out_dir / 'metadata.yaml'} (parity_gate_passed={parity_gate_passed})")

    metrics_src = compare_path.parent / "metrics_full.json"
    metrics_dst = out_dir / "metrics_full.json"
    if metrics_src.is_file():
        import shutil

        shutil.copy2(metrics_src, metrics_dst)
        print("Wrote %s (from compare dir)" % metrics_dst)
    else:
        import json as _json
        from datetime import datetime, timezone

        delta = None
        if baseline_rate is not None and pf_rate is not None:
            try:
                delta = round(float(pf_rate) - float(baseline_rate), 6)
            except (TypeError, ValueError):
                pass
        stub = {
            "schema_version": "metrics_full/1.0",
            "experiment_id": args.experiment_id or "exp-step2-lite-smoke",
            "generated_at_utc": datetime.now(timezone.utc).isoformat(),
            "note": "metrics_full.json missing next to compare.json; run compare_runs.py on same --out as compare.json",
            "solve_rates": {
                "baseline": baseline_rate,
                "pf": pf_rate,
                "delta": delta,
            },
        }
        metrics_dst.write_text(_json.dumps(stub, indent=2), encoding="utf-8")
        print("Wrote %s (stub; full run card from compare_runs preferred)" % metrics_dst)

    # Assert we produced the bundle shape defined in publish_bundle (verifier expects this).
    for f in EXPORT_PRODUCES_FILES:
        if not (out_dir / f).exists():
            print("Error: export did not produce %s" % f, file=sys.stderr)
            sys.exit(1)
    for d in EXPORT_PRODUCES_DIRS:
        if not (out_dir / d).is_dir():
            print("Error: export did not produce %s/" % d, file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
