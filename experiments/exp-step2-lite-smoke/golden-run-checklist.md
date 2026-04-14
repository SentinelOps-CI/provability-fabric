# Golden Step-2 run checklist

Run a true golden baseline+PF pair and freeze it: all gates pass, run-ids.md updated only via the script.

## 0.1 Run the canonical pipeline (WSL/Linux)

From repository root in WSL or Linux:

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids
```

Do not run on Windows-native; OpenHands and the harness require Unix.

## 0.2 Golden invariants (copy into run notes)

After a successful run you must be able to point to these exact artifacts:

| Artifact | Path |
|----------|------|
| Baseline predictions | `runs/exp_step2_lite_smoke/baseline/predictions.jsonl` |
| PF predictions | `runs/exp_step2_lite_smoke/pf/predictions.jsonl` |
| Baseline eval | `runs/exp_step2_lite_smoke/baseline/eval/**` |
| PF eval | `runs/exp_step2_lite_smoke/pf/eval/**` |
| Compare report | `runs/exp_step2_lite_smoke/compare.json` and `compare.csv` |
| Run IDs (script-updated) | `experiments/exp_step2_lite_smoke/run-ids.md` updated by the script, not manually |

## Acceptance checks (hard)

- **compare.json:** `baseline.solve_rate` and `pf.solve_rate` are numbers (not null).
- **compare.json:** `patch_apply.applies_false == 0`.
- **validate_pf_run.py** exits 0 for the PF run dir (e.g. `python bench/swebench/validate_pf_run.py runs/exp_step2_lite_smoke/pf/<run_id>`).
- **check_no_stub.py** exits 0 (e.g. `python experiments/scripts/check_no_stub.py runs/exp_step2_lite_smoke/baseline runs/exp_step2_lite_smoke/pf`).

If any check fails on first attempt, do not change docs. Fix the pipeline until all pass; everything else depends on having one trusted reference run.
