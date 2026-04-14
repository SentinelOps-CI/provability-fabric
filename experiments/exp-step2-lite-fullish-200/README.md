# exp_step2_lite_fullish_200

Larger slice: 200 instances from SWE-bench Lite (test split), deterministic seed. Same manifest discipline, harness, and compare gates as smoke and medium.

## Setup

1. Generate instance list: `python experiments/scripts/sample_lite_instance_ids.py --count 200 --seed 42` and write to `experiments/exp_step2_lite_fullish_200/instance_ids.txt`.
2. Copy and adapt manifest from smoke; set `experiment_id` to `exp_step2_lite_fullish_200`.
3. Run pipeline with `--instance-ids-file experiments/exp_step2_lite_fullish_200/instance_ids.txt` and `--experiment-dir experiments/exp_step2_lite_fullish_200`.

## Acceptance gates by scale

- **Max acceptable solve-rate drop (absolute):** 0.03.
- **patch_apply.applies_false:** 0.
- **Timeout/empty-patch regression:** Monitor stress_summary.json; document and fix sustained regressions.
