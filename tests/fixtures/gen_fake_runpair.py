# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Synthetic fixture generator for experiment scripts tests (no Docker, no OpenHands).
# Builds a temp tree: baseline/, pf/ with predictions.jsonl, run_id/instance_id/ artifacts,
# and baseline/eval/, pf/eval/ harness report JSON.

from __future__ import annotations

import json
import tempfile
from pathlib import Path
from typing import List


DIFF_STUB = """diff --git a/foo.py b/foo.py
index 1234567..abcdefg 100644
--- a/foo.py
+++ b/foo.py
@@ -1,3 +1,4 @@
+import os
 def main():
     pass
"""


def make_fake_runpair(
    run_id: str = "fake-run-001",
    instance_ids: List[str] | None = None,
    n_resolved_baseline: int = 2,
    n_resolved_pf: int = 1,
    n_applies_false: int = 0,
    stub_in_patch: bool = False,
    summary_model_name: str = "gpt-4o",
    write_harness_sidecars: bool = True,
) -> Path:
    """
    Create a temp directory with baseline/ and pf/ runpair layout.
    Returns the path to the temp root.

    - instance_ids: list of instance IDs (default: ["inst_a", "inst_b", "inst_c"])
    - n_resolved_baseline: number of resolved in baseline eval report
    - n_resolved_pf: number of resolved in PF eval report
    - n_applies_false: number of patch_apply_check with applies=False (first N instances)
    - stub_in_patch: if True, put .swebench_stub in one model.patch for check_no_stub tests
    - summary_model_name: model string written into summary/cost fixtures (pricing gate tests)
    - write_harness_sidecars: run_status.json under baseline/ and pf/, eval_metadata.json in eval dirs
    """
    if instance_ids is None:
        instance_ids = ["inst_a", "inst_b", "inst_c"]
    root = Path(tempfile.mkdtemp(prefix="pf_fake_runpair_"))
    baseline_dir = root / "baseline"
    pf_dir = root / "pf"
    baseline_dir.mkdir(parents=True)
    pf_dir.mkdir(parents=True)

    def write_predictions(dest_dir: Path) -> None:
        pred_path = dest_dir / "predictions.jsonl"
        lines = []
        for iid in instance_ids:
            patch = DIFF_STUB + ("\n.swebench_stub\n" if stub_in_patch and iid == instance_ids[0] else "")
            lines.append(json.dumps({
                "instance_id": iid,
                "model_patch": patch,
                "model_name_or_path": "pf-swebench-openhands",
            }, ensure_ascii=False))
        pred_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    def write_instance_artifacts(
        run_root: Path,
        applies_false_indices: set[int],
        with_compliance: bool,
    ) -> None:
        run_id_dir = run_root / run_id
        run_id_dir.mkdir(parents=True)
        for i, iid in enumerate(instance_ids):
            safe_id = "".join(c if c.isalnum() or c in "-_" else "_" for c in iid)
            inst_dir = run_id_dir / safe_id
            inst_dir.mkdir(parents=True)
            patch_content = DIFF_STUB + ("\n.swebench_stub\n" if stub_in_patch and iid == instance_ids[0] else "")
            (inst_dir / "model.patch").write_text(patch_content, encoding="utf-8")
            (inst_dir / "metadata.json").write_text(json.dumps({
                "instance_id": iid,
                "run_id": run_id,
                "policy_hash": "abc123" if with_compliance else None,
            }, indent=2), encoding="utf-8")
            applies = i not in applies_false_indices
            (inst_dir / "patch_apply_check.json").write_text(json.dumps({
                "applies": applies,
                "stderr": "" if applies else "patch failed to apply",
            }, indent=2), encoding="utf-8")
            (inst_dir / "cost_report.json").write_text(json.dumps({
                "instance_id": iid,
                "model_name": summary_model_name,
                "prompt_tokens": 10,
                "completion_tokens": 20,
                "wall_clock_s": 1.5,
                "tool_calls": 2,
            }, indent=2), encoding="utf-8")
            if with_compliance:
                evidence_dir = inst_dir / "evidence"
                evidence_dir.mkdir(parents=True, exist_ok=True)
                (evidence_dir / "events.jsonl").write_text(
                    json.dumps({"event_type": "run_started", "run_id": run_id}) + "\n",
                    encoding="utf-8",
                )
                (inst_dir / "policy_compliance_summary.json").write_text(json.dumps({
                    "compliant": True,
                    "violations": 0,
                    "run_id": run_id,
                    "reason_codes": [],
                }, indent=2), encoding="utf-8")

        summary_instances = [
            {
                "instance_id": iid,
                "model_name": summary_model_name,
                "prompt_tokens": 10,
                "completion_tokens": 20,
                "wall_clock_s": 1.5,
                "tool_calls": 2,
            }
            for iid in instance_ids
        ]
        (run_id_dir / "summary.json").write_text(json.dumps({
            "run_id": run_id,
            "guarded": with_compliance,
            "n_instances": len(instance_ids),
            "instances": summary_instances,
        }, indent=2), encoding="utf-8")

    applies_false_indices = set(range(min(n_applies_false, len(instance_ids))))

    write_predictions(baseline_dir)
    write_instance_artifacts(baseline_dir, applies_false_indices, with_compliance=False)

    write_predictions(pf_dir)
    write_instance_artifacts(pf_dir, applies_false_indices, with_compliance=True)

    def write_eval_report(eval_dir: Path, resolved_count: int) -> None:
        eval_dir.mkdir(parents=True, exist_ok=True)
        resolved = list(instance_ids)[:resolved_count]
        unresolved = [iid for iid in instance_ids if iid not in resolved]
        report = {
            "resolved_ids": resolved,
            "total_instances": len(instance_ids),
            "unresolved_ids": unresolved,
            "error_ids": [],
            "empty_patch_ids": [],
        }
        (eval_dir / "model.report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
        if write_harness_sidecars:
            (eval_dir / "eval_metadata.json").write_text(
                json.dumps({"run_id": run_id, "predictions_sha256": ""}, indent=2),
                encoding="utf-8",
            )

    write_eval_report(baseline_dir / "eval", n_resolved_baseline)
    write_eval_report(pf_dir / "eval", n_resolved_pf)

    if write_harness_sidecars:
        for pred_root in (baseline_dir, pf_dir):
            (pred_root / "run_status.json").write_text(
                json.dumps({"run_id": run_id}, indent=2),
                encoding="utf-8",
            )

    return root
