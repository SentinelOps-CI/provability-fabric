# Regression eradication loop (Phase 2)

When the golden run gates fail (e.g. `pf.solve_rate < baseline.solve_rate - threshold`) or any gate in **golden-cycle.md** section 0.2 fails, do not write "golden" anywhere. Enter this loop and iterate until parity and replay pass.

**References:** Run IDs and compare flow: **experiments/exp-step2-lite-smoke/commands.md**. Fix strategy and buckets: **docs/internal/pf-solve-rate-debugging.md**. Golden gates: **experiments/exp-step2-lite-smoke/golden-cycle.md**.

---

## 2.1 Generate the regression slice

From repository root (WSL/Linux), with baseline and PF run dirs from **experiments/exp-step2-lite-smoke/run-ids.md** (or the run you just compared):

```bash
make swebench-regressions \
  BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<pf_run_id>
```

**Requires:** `runs/exp-step2-lite-smoke/compare.csv` (from `compare_runs.py`). The Makefile runs:

1. **list_delta_cases.py** – writes `runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt` (one instance_id per line).
2. **extract_case_bundle.py** – for each instance in that file, extracts case bundles into `runs/exp-step2-lite-smoke/analysis/cases/`.
3. **bucket_pf_failures_from_cases.py** – writes `runs/exp-step2-lite-smoke/analysis/pf_failure_buckets.csv` (instance_id, bucket, pf_status, baseline_status, violations, reason_codes, notes).

**Outputs to verify:**

- `analysis/baseline_solved_pf_failed.txt` (non-empty if there is a regression).
- `analysis/cases/` (extracted case bundles per instance).
- `analysis/pf_failure_buckets.csv` (buckets: policy_denial_or_violation, empty_patch_or_patch_write_failed, budget_timeout, patch_format_or_apply, agent_quality_or_missing_tooling, needs_manual_read).

---

## 2.2 Fix in leverage order (do not weaken security)

Apply fixes in this order. Do not relax network or confinement to fix regressions.

| Order | Fix | Action |
|-------|-----|--------|
| **1** | **Agent recovery on denial** | Stop treating denial as fatal. Adjust the OpenHands engine wrapper so denial (e.g. exit 125) is "command failed, continue planning" and the agent can try permitted alternatives. |
| **2** | **Allowlist local tooling** | Add missing local commands: `pytest`, `pip -e`, `make`, `ruff`, etc. Still no network. |
| **3** | **Budget symmetry** | If you raise timeout or max steps for PF, raise the same for baseline so comparison is fair. |
| **4** | **Patch extraction correctness** | Apply-check parity is mandatory. Ensure `patch_apply_check.json` and harness use the same apply logic; fix runner/harness so applies_false is 0. |

Details and bucket-specific guidance: **docs/internal/pf-solve-rate-debugging.md**.

---

## 2.3 Rerun only the regression slice, then re-harness + re-compare

1. **Rerun PF guarded** on the regression slice only (same instance set as `analysis/baseline_solved_pf_failed.txt`). Use the same manifest and budget as the experiment; do not reduce baseline budget.

   Example (runner and paths as in commands.md; use your RUN_CMD and experiment dir):

   ```bash
   # Create an instance list for the regression slice only.
   cp runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt /tmp/regression_instance_ids.txt

   $RUN_CMD \
     --dataset Lite \
     --instance-ids-file /tmp/regression_instance_ids.txt \
     --experiment-dir experiments/exp-step2-lite-smoke \
     --engine openhands \
     --seed 42 \
     --out runs/exp-step2-lite-smoke/pf/predictions_regression.jsonl \
     --runs-dir runs/exp-step2-lite-smoke/pf
   ```

   Then merge or replace the PF predictions for those instances back into the full PF run so the full compare is consistent (or run a slice-only compare if your tooling supports it).

2. **Re-run harness** on the updated PF run (and baseline if you changed anything): same eval dirs as in commands.md (e.g. `run_swebench_eval.py` for baseline and PF).

3. **Re-run compare** with strict gates:

   ```bash
   make swebench-compare \
     BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
     PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<pf_run_id>
   ```

4. **Check gates** (golden-cycle.md 0.2): `compare.json` has numeric solve rates, `patch_apply.applies_false == 0`, no budget_drift, policy and replay sections present, and **`make swebench-compare`** passes **`--require-priced-models`** (same as the full cycle). Run **verify_publish_bundle.py** if you are about to export.

5. **Repeat** from 2.1 until:
   - Parity gate passes (`pf.solve_rate >= baseline.solve_rate - threshold`), and
   - Replay success is high and mismatches are explainable or rare.

Only after all gates pass, run with `--update-run-ids` (or call **update_run_ids_if_green.py**) to update run-ids.md and produce the publish bundle.
