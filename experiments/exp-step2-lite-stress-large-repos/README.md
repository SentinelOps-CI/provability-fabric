# exp-step2-lite-stress-large-repos

Stress slice of 5–10 **known-heavy** SWE-bench Lite instances (django, astropy, sympy, scikit-learn, matplotlib, sphinx) for validating that pipeline and policy improvements reduce empty-patch rates over time.

**Purpose:** Manual or scheduled runs only. Not gated in CI. Use the same flow as `exp-step2-lite-smoke` (baseline run, PF run, validations, harness, compare). Compare `empty_patch_reasons_topN` in `compare.json` across runs to see whether diff timeouts, patch-too-large, or apply-check failures decrease after changes.

**Usage:** From repo root (WSL/Linux), run baseline and PF with this experiment dir and `--instance-ids-file experiments/exp-step2-lite-stress-large-repos/instance_ids.txt`. Run harness and compare as in `experiments/exp-step2-lite-smoke/commands.md`. Increase `--openhands-timeout` or manifest `timeout_sec` if large repos time out.

**Do not** add this experiment to PR or nightly gates; it is for periodic human review and trend analysis.
