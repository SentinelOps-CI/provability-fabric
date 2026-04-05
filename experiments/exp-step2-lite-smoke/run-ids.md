# Recorded run IDs (Case 1.1 / 1.2)

Use these in compare (Case 1.3/1.4) and for `validate_pf_run.py`.

**Canonical way to update:** run `python experiments/scripts/update_run_ids_if_green.py --experiment-dir experiments/exp-step2-lite-smoke --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<run_id> --pf-run-dir runs/exp-step2-lite-smoke/pf/<run_id>` (and optionally `--instance-ids-file`, `--expected-count`). This script only writes run-ids.md when all gates pass (validate_predictions, check_no_stub, validate_pf_run, compare_runs with --require-harness --require-compliance --require-patch-apply). Use **`--allow-empty-patch`** when some instances have empty patches (e.g. OpenHands produced no diff); the cycle script (`run-baseline-pf-cycle.sh --update-run-ids`) passes this flag automatically.

| Run   | run_id |
|-------|--------|
| Baseline (Case 1.1) | `20260317-120041-1badcd73` |
| PF-guarded (Case 1.2) | `20260317-143046-340fb140` |

Compare command (replace run IDs with your new baseline and PF run IDs if needed):

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/20260317-120041-1badcd73 \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/20260317-143046-340fb140
```
