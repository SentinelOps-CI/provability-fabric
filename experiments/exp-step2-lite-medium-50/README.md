# exp_step2_lite_medium_50

Medium slice: 50 deterministic instance IDs from SWE-bench Lite (test split), round-robin across repos, fixed seed. Same manifest discipline, harness, and compare gates as exp_step2_lite_smoke.

## Setup

1. Generate instance list (from repo root, with `datasets` installed):
   ```bash
   python experiments/scripts/sample_lite_instance_ids.py --count 50 --seed 42
   ```
   Copy or move the output to `experiments/exp_step2_lite_medium_50/instance_ids.txt`.

2. Copy and adapt manifest from smoke: same schema as `experiments/exp_step2_lite_smoke/manifest.json`; set `experiment_id` to `exp_step2_lite_medium_50`, keep `seed=42`, `budgets`, `policy_pack`, `model_params`.

3. Run the same pipeline as smoke with `--instance-ids-file experiments/exp_step2_lite_medium_50/instance_ids.txt` and `--experiment-dir experiments/exp_step2_lite_medium_50`. Runs go under `runs/exp_step2_lite_medium_50/`.

## Acceptance gates by scale

- **Max acceptable solve-rate drop (absolute):** 0.02 (pf.solve_rate >= baseline.solve_rate - 0.02).
- **patch_apply.applies_false:** 0 (same as smoke).
- **Timeout/empty-patch regression:** Compare stress_summary.json across runs; do not accept a sustained increase in timeout_rate_pf or in empty_patch_reasons_topN for guard_denial or diff_timeout without a documented fix.
