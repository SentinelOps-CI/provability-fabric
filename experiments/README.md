# Experiment manifests

Experiment manifests fix configuration (PF commit, agent version, model, policy, budgets, seed) so that when solve rates differ between baseline and PF-guarded runs, you can attribute the difference to the run mode rather than drift.

## Manifest schema

Each experiment lives under `experiments/<experiment_id>/` with a `manifest.json` containing:

| Field | Description |
|-------|-------------|
| `experiment_id` | Short identifier (e.g. `exp-step2-lite-smoke`). |
| `pf_commit` | Git SHA of the Provability-Fabric repo at run time. Fill before or after the run so results are tied to a known PF version. |
| `agent_framework` | `openhands` or `swe-agent`. |
| `agent_commit` | Git SHA or tag of the agent framework (e.g. OpenHands) when installed from source. |
| `agent_image_tag` | Docker image tag if the agent is run from a container; alternative to `agent_commit`. |
| `model` | `{ "id": "gpt-4o-mini", "provider": "openai" }` – exact model ID and provider. |
| `dataset` | e.g. `swebench_lite`. |
| `dataset_split` | e.g. `test`. |
| `policy_pack` | Policy pack name (e.g. `swebench_safe_v1`) when running PF-guarded. |
| `budgets` | `max_steps`, `max_tool_calls`, `timeout_sec` – must match policy and runner flags. |
| `model_params` | `temperature`, `top_p` (or null) – fixed for reproducibility. |
| `seed` | Fixed integer for any RNG (e.g. OpenHands, sampling). |
| `run_modes` | List of modes for this experiment: `["baseline", "pf_guarded"]`. |

## Platform: WSL/Linux required for Step 2

You cannot finish Step 2 (real run + harness) on Windows-native: OpenHands uses **fcntl**, the SWE-bench harness uses **resource**, and Docker is required by the harness. Move the entire real run + harness loop to **WSL (Ubuntu recommended) or Linux**.

Before proceeding to runs, verify the minimal environment: see **experiments/exp-step2-lite-smoke/env-checklist.md** and run **`python3 experiments/scripts/check_wsl_env.py`** from the repository root (minimal Debian/GCP images often lack a `python` shim; after **`source .venv-wsl/bin/activate`**, **`python`** works). If any check fails, do not proceed.

**One-shot orchestration (WSL/Linux):** From repo root, run `bash experiments/scripts/run-baseline-pf-cycle.sh` to execute the full "first valid baseline + PF pair" workflow (env check, manifest fill, baseline run, PF run, validations, harness, **replay sample** (run_replay_sample.py writes replay_summary.json), compare with gates, delta lists, case extraction, bucketing). Use `--update-run-ids` to update **run-ids.md** in `experiments/exp-step2-lite-smoke/` when compare passes (and to run export_publish_artifacts, write publish/PUBLISH.md, **publish/GOLDEN.ok**, **publish/RESULTS.md**, **publish/VERIFY.md**, and append to **experiments/scale-results-ledger.jsonl**); use `--triage` to run list_delta_cases and extract_case_bundle. Requires `pf` CLI and OpenHands; see **experiments/exp-step2-lite-smoke/commands.md** for manual steps and "Without pf CLI" alternatives. **Golden cycle:** One trusted reference run; see **experiments/exp-step2-lite-smoke/golden-cycle.md** for the canonical command, required artifacts, and acceptance checks. When gates fail, follow **experiments/regression-loop.md**. **Verification:** **experiments/VERIFICATION_PLAN.md** maps each plan requirement to implementation. **Machine verifier:** `experiments/scripts/verify_publish_bundle.py` (no network/Docker); fixture in `experiments/fixtures/verify_publish_bundle/`; CI: `.github/workflows/verify-publish-bundle.yaml`. **Local tests (no WSL):** `python experiments/scripts/run_verification_tests.py`.

**Makefile shortcuts (repo root):** `make swebench-step2` runs the canonical script (WSL/Linux only). `make swebench-compare`, `make swebench-triage`, and **`make swebench-regressions`** require `BASELINE_RUN_DIR` and `PF_RUN_DIR` (from run-ids.md). **`make swebench-compare`** passes the same golden compare gates as **`run-baseline-pf-cycle.sh`** Phase 4.3: `--require-harness`, `--require-compliance`, `--require-patch-apply`, and **`--require-priced-models`**. `swebench-regressions` runs list_delta_cases, extract_case_bundle, and bucket_pf_failures_from_cases for the baseline_solved_pf_failed slice. See **experiments/exp-step2-lite-smoke/commands.md** "Canonical entrypoint and Makefile".

## Command reference (runbook)

Order of operations for a full SWE-bench + PF cycle (WSL/Linux):

1. **Env check:** `python3 experiments/scripts/check_wsl_env.py` (see **experiments/exp-step2-lite-smoke/env-checklist.md**).
2. **Preflight (optional):** `pf bench swebench run --dataset Lite --split test --max_instances 5 --preflight` to materialize workspaces and see repo-size hints (see **bench/swebench/README.md** for runner options).
3. **Baseline run:** See **experiments/exp-step2-lite-smoke/commands.md** Case 1.1 (`pf bench swebench run ... --engine openhands`).
4. **PF run:** See **experiments/exp-step2-lite-smoke/commands.md** Case 1.2 (`pf bench swebench run ... --guarded --policy swebench_safe_v1`).
5. **Validations:** `validate_predictions` (baseline + PF), `check_no_stub`, `validate_pf_run`; see commands.md.
6. **Harness:** Run SWE-bench evaluation on both prediction sets; see commands.md Case 1.3.
7. **Compare:** `compare_runs.py` with `--require-harness --require-compliance --require-patch-apply --require-priced-models` for golden parity; see commands.md Case 1.3/1.4. Output **`compare.json`** includes **`meta`** (generated time, run dir paths); use **`jq '.meta, .patch_apply'`** — not **`jq '.summary'`** (that key does not exist). After overnight runs, re-run compare with the correct **`--baseline-run-dir`** / **`--pf-run-dir`**. **`run_health_snapshot.py`** summarizes one **`runs/<run_id>`**; **`smoke_direct_agent_one.sh`** is a one-instance **`direct_agent`** check (see **bench/swebench/README.md** and **exp-step2-lite-smoke/env-checklist.md**).
8. **Update run IDs and export (on green):** `python experiments/scripts/update_run_ids_if_green.py ...` (or use `run-baseline-pf-cycle.sh --update-run-ids`). Writes run-ids.md, runs export_publish_artifacts, publish/GOLDEN.ok, RESULTS.md, VERIFY.md, and appends to **experiments/scale-results-ledger.jsonl** (see **experiments/scale-results-ledger.md** and **experiments/scripts/append_scale_results_ledger.py**).

Runner options (dataset, instance filters, timeouts): **bench/swebench/README.md**. If baseline or PF runs produce empty patches and the trajectory has only MessageEvent (no ActionEvent), next steps are on the OpenHands side: **experiments/exp-step2-lite-smoke/openhands-headless-troubleshooting.md** (version check, minimal headless test, model override, GUI comparison). **Automated verification** of provider routing, eval cleanup scoping, compare strict gates, and timeout defaults: **`docs/internal/swebench-stabilization-regression-matrix.md`** (pytest command list and WSL smoke checklist).

## Usage

1. **Fill manifest**: Set `pf_commit` (and optionally `agent_commit`) before or after the run. From repo root:
   ```bash
   python experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json
   ```
   To also copy the filled manifest into a run directory (store alongside results):
   ```bash
   python experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json runs/<run_id>
   ```
   The script sets `pf_commit` from `git rev-parse HEAD` and `created_at`; if `OPENHANDS_COMMIT` or `AGENT_COMMIT` is set, it fills `agent_commit`.
2. **Run baseline and PF-guarded**: Exact commands for exp-step2-lite-smoke (including `--openhands-max-iterations`, `--openhands-timeout`, instance list) are in **experiments/exp-step2-lite-smoke/commands.md** (Case 1.1 and 1.2). Record each run_id.
3. **Store manifest with results**: Run the fill script with the run_dir argument so `runs/<run_id>/experiment_manifest.json` is written and the run is tied to the exact config.

Filling `pf_commit` and `agent_commit` (or `agent_image_tag`) before comparing runs ensures that a 2–4 point solve-rate difference is not due to commit or image drift. **Reproducibility:** Dataset and OpenHands version drift can also affect solve rates. The runner writes `runs/<run_id>/env.json` (openhands_version, datasets_version, swebench_version, pip_freeze_hash); compare reports **env_drift** when baseline and PF envs differ. For golden and release runs, pin `datasets`, `swebench`, and `openhands` versions (e.g. in requirements or CI); see **bench/swebench/README.md** "Reproducibility".

## Stress slice (exp-step2-lite-stress-large-repos)

The directory `experiments/exp-step2-lite-stress-large-repos/` contains a manifest and `instance_ids.txt` for 5–10 known-heavy repos (django, astropy, sympy, scikit-learn, matplotlib, sphinx). Use it for **manual or scheduled** runs to validate that improvements reduce empty-patch rates; compare `empty_patch_reasons_topN` in `compare.json` across runs. Not gated in CI. A **scheduled GitHub Action** (`.github/workflows/bench-swebench-stress-scheduled.yaml`) runs weekly (Sunday 03:00 UTC) and on `workflow_dispatch`; it runs the stress experiment, harness, and compare, then **`experiments/scripts/summarize_stress_run.py`** to write **stress_summary.json** (schema_version, pf_commit, agent_commit, dataset_id, dataset_version, harness_id; timeout_rate_*, wall_clock_s_median/p95, guard_overhead_s_median, empty_patch_reasons_topN, solve rates). The workflow uploads compare.json, stress_summary.json, compare.csv and uploads **stress_summary.json** as the named artifact **stress-summary**. A **Stress regression alerts** step runs **check_stress_alerts.py**; thresholds are in **experiments/config/stress_alerts.yaml** (optional; script uses built-in defaults if missing). Ledger row shape is defined in **experiments/schemas/scale_results_ledger_row.schema.json** (append_scale_results_ledger validates each row before append). See **experiments/config/README.md**. Schema: **experiments/schemas/stress_summary.schema.json**. See that directory's README.

## Expanded slices (medium and fullish)

**experiments/exp-step2-lite-medium-50/** and **experiments/exp-step2-lite-fullish-200/** provide 50- and 200-instance slices with the same manifest discipline, harness, and compare gates as smoke. Generate instance_ids.txt with `sample_lite_instance_ids.py --count 50 --seed 42` (or 200). See each directory's README for setup and acceptance gates by scale.

## Deterministic instance slice (exp-step2-lite-smoke)

The file `experiments/exp-step2-lite-smoke/instance_ids.txt` contains 20 instance IDs from SWE-bench Lite (test split), one per line. This list is **stable** for the whole iteration loop (baseline vs PF-guarded, reruns). Do not change it during an experiment iteration.

- **Sampling**: Random sample with fixed seed (42, matching the manifest) and **round-robin across repos** so multiple repos are represented. No cherry-picking.
- **Regenerate**: From repo root, with `datasets` installed (`pip install datasets`):
  ```bash
  python experiments/scripts/sample_lite_instance_ids.py --count 20 --seed 42
  ```
  Output is written to `experiments/exp-step2-lite-smoke/instance_ids.txt`.
- **Broken-harness exclusion**: The script supports `--exclude-file <path>` (one instance_id per line). The repo does not currently ship a list of known broken-harness IDs; if you add one, pass it when regenerating.
- **Runner**: Pass IDs as comma-separated, e.g. `--instance_ids $(cat experiments/exp-step2-lite-smoke/instance_ids.txt | tr '\n' ',')` (strip trailing comma if needed), or build the list in your experiment script from the file lines.

## SWE-bench harness evaluation (baseline vs PF)

Use the **same** SWE-bench harness for both baseline and PF predictions. Step-by-step commands (including wrapper and direct `swebench.harness.run_evaluation`) are in **experiments/exp-step2-lite-smoke/commands.md** (Case 1.3). Requires `swebench` and Docker.

**Collect results** (pass/fail per instance and failure buckets):

```bash
python experiments/scripts/collect_eval_results.py \
  runs/exp-step2-lite-smoke/baseline/eval \
  runs/exp-step2-lite-smoke/pf/eval
```

Use `--json` for machine-readable summary; `--csv out.csv` for per-instance (instance_id, run_label, status).

## Comparison report (one command, reproducible)

Aggregates baseline/pf eval, run summaries, cost reports, policy compliance, and patch_apply_check into `compare.json` and `compare.csv`. Exact command and options: **experiments/exp-step2-lite-smoke/commands.md** (Case 1.3 and 1.4). Run compare after the harness (Case 1.3) so that solve rates are populated. Use **`--require-harness`**, **`--require-compliance`**, **`--require-patch-apply`**, and **`--require-priced-models`** for the same gates as the canonical cycle (`patch_apply.applies_false` must be 0 for Step 2 parity). **Canonical way to update run-ids.md:** run `python experiments/scripts/update_run_ids_if_green.py --experiment-dir experiments/exp-step2-lite-smoke --baseline-run-dir <path> --pf-run-dir <path>` (or with --instance-ids-file; add **--allow-empty-patch** when some instances have empty patches). The **cycle script** (`run-baseline-pf-cycle.sh --update-run-ids`) invokes this with **--allow-empty-patch** so runs with some empty-patch instances can still update run-ids. The script runs all gates (validate_predictions, check_no_stub, validate_pf_run, compare_runs with --require-harness --require-compliance --require-patch-apply --require-priced-models) and only then writes or updates **experiments/exp-step2-lite-smoke/run-ids.md**. When gates pass, the script also runs **export_publish_artifacts.py** (which produces the bundle shape defined in **experiments/scripts/publish_bundle.py**) and uses **experiments/scripts/publish_docs.py** to write **publish/PUBLISH.md**, **publish/GOLDEN.ok** (run IDs, pf_commit, timestamp, parity_gate_passed), **publish/RESULTS.md**, and **publish/VERIFY.md** so every green run produces a ready-to-share artifact folder. The publish bundle shape and GOLDEN.ok keys are defined in **experiments/scripts/publish_bundle.py** and used by both **verify_publish_bundle.py** and **export_publish_artifacts.py**. The verifier (**verify_publish_bundle.py**) checks the bundle against those constants and **compare_gates.py** for compare.json gates. **Scale Results Ledger:** **experiments/scripts/append_scale_results_ledger.py** appends one row per run to **experiments/scale-results-ledger.jsonl**; each row is validated against **experiments/schemas/scale_results_ledger_row.schema.json** before append. See **experiments/SCALE_RESULTS_LEDGER.md**. The update_run_ids_if_green script invokes it on green. Outputs (default under `--experiment-dir`, overridable with `--out`):

- **compare.json**: solve rates, delta, cost_per_solved (tokens, wall_clock_s, tool_calls), PF violation rates, replay_success_rate (when replay bundles exist), patch_apply aggregation (total, applies_true, applies_false, errors_topN), violation_reasons_top10, **empty_patch_reasons_topN** (counts per reason code: agent_no_changes, patch_too_large, diff_timeout, apply_check_failed, workspace_missing_or_failed, guard_denial_prevented_writes), and when both run dirs exist **env_drift** (differing keys between baseline and PF run `env.json`). When eval_metadata.json exists in eval dirs, compare also emits **reproducibility** fields: dataset_name, split, datasets_version, swebench_version, harness_dataset_id, openhands_version (from run dir env.json). When **replay_summary.json** exists in the output dir (written by run_replay_sample.py), compare merges **replay** (sample_size, success_rate, mismatch_count, replay_fail_reasons_topN). run_replay_sample.py also writes **replay/instance_results.jsonl** (per instance: patch hashes, match, failure_reason); it replays all PF-resolved zero-violation instances when count ≤20, otherwise a deterministic seeded sample (e.g. 25–50). When PF run dir exists, compare adds **policy** (reason_codes_topN, denied_commands_topN, commands_seen_topN) and **denial recovery** (denials_total_pf, episodes_aborted_after_denial_pf, recovered_after_denial_pf_rate). The report shape is defined by **experiments/schemas/compare_report.schema.json**; if the `jsonschema` package is installed, compare_runs validates the written report and exits with error on mismatch.
- **compare.csv**: per-instance rows (including baseline_patch_applies, pf_patch_applies) plus `_summary` row; pivot-friendly.
- **harness_eval (compare.json):** Per-instance test runtime (seconds) from SWE-bench `run_instance.log` (`Test runtime: N seconds`). Each side has `n_parsed` (instances with a parseable log) and `n_instances_in_report` (total in the harness run report). When the harness fails for some instances (e.g. Docker/network errors such as accept4 failed 110), `n_parsed` can be lower than `n_instances_in_report`; re-run the harness or fix the environment (Phase 1.1, run_swebench_eval) if the gap is large.

**JSON schemas:** `experiments/schemas/compare_report.schema.json` (compare output); `experiments/schemas/harness_report_min.schema.json` (minimum harness report: resolved_ids or resolved_instances, total_instances).

**Acceptance gate:** `compare.json` must have numeric `baseline.solve_rate` and `pf.solve_rate` (not null). If they are null, run the harness first and ensure reports exist under `baseline/eval` and `pf/eval`, then run compare again.

**Acceptance gates by scale:** The parity gate is `pf.solve_rate >= baseline.solve_rate - 0.01` (absolute drop at most 1%). For larger slices (e.g. 50, 200 instances), define once and document: (1) **Max acceptable solve-rate drop** (absolute, e.g. 0.01 for smoke, 0.02 for medium, 0.03 for fullish). (2) **Max acceptable increase** in timeouts or empty-patch rate (e.g. stress_summary.json timeout_rate_pf and empty_patch_reasons_topN must not regress beyond a chosen threshold). Put these in the experiment README (e.g. `experiments/exp-step2-lite-medium-50/README.md`) and in CI or release checklists so regressions are caught.

Omit `--baseline-run-dir` or `--pf-run-dir` when only one run exists; metrics are filled where possible.

**Run/eval binding (--require-harness):** When `--require-harness` is set, compare_runs enforces that the eval dirs correspond to the run that produced the predictions: it reads `run_status.json` from the predictions directory (e.g. `experiment_dir/baseline/run_status.json`), asserts that the provided run dir name equals that run_id, and that `eval_metadata.json` in each eval dir (written by run_swebench_eval.py after the harness) has the same run_id. **Stale-eval check:** If the predictions file timestamp is newer than the eval report timestamp, compare fails (re-run harness before compare). If the predictions file has a sidecar `predictions.sha256`, compare verifies it matches the hash recorded in eval_metadata so that eval was run on the same predictions file. **Budget drift:** When both baseline and PF run dirs contain `experiment_manifest.json`, compare asserts that timeout_sec, max_steps, max_tool_calls, model, and model_params match; on mismatch it sets report["budget_drift"] and exits with error. A wrong pairing (e.g. baseline eval with PF run dir) fails with a clear run_id or predictions_sha256 mismatch error.

## Post-run validation

After a run that writes `predictions.jsonl` (e.g. baseline or PF-guarded), run:

```bash
python experiments/scripts/validate_predictions.py runs/exp-step2-lite-smoke/baseline/predictions.jsonl -n 20 --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt
```

Add **`--allow-empty-patch`** when some instances produced no patch (e.g. OpenHands failed to produce a diff); the cycle script uses this for Phase 2.2/3.2 and for Phase 5a (update_run_ids_if_green). Checks: JSONL line count equals 20; every `instance_id` appears exactly once and is in the instance list; each `model_patch` is a non-empty diff (unless `--allow-empty-patch`); `predictions.pfmeta.jsonl` (if present) has the same line count and matching `instance_id` order. If a **run_status.json** exists in the same directory as the predictions file (written by the runner) and its `status` is not `complete`, validation fails unless `--allow-partial` is set (use that only when intentionally validating a partial or failed run).

**Stub check (mandatory for evaluation):** If any `model.patch` under the run dirs contains `.swebench_stub`, the run is invalid. After baseline and PF runs, run:

```bash
python experiments/scripts/check_no_stub.py runs/exp-step2-lite-smoke/baseline runs/exp-step2-lite-smoke/pf
```

If this exits non-zero, do not use the run for evaluation; the pipeline must use real OpenHands (no stub fallback).

## Scripts and shared modules

- **publish_docs.py** – Builds PUBLISH.md, RESULTS.md, and VERIFY.md content (build_publish_md, build_results_md, build_verify_md). Used by update_run_ids_if_green.py; content is testable without I/O.
- **publish_bundle.py** – Single definition of a valid publish bundle: PUBLISH_BUNDLE_REQUIRED_FILES, PUBLISH_BUNDLE_REQUIRED_DIRS, GOLDEN_OK_REQUIRED_KEYS, EXPORT_PRODUCES_FILES/DIRS. Used by verify_publish_bundle.py and export_publish_artifacts.py.
- **compare_gates.py** – check_compare_gates(compare) returns list of gate-failure messages (solve rates numeric, patch_apply.applies_false == 0, replay.success_rate present, policy section). Used by verify_publish_bundle.py.
- **check_stress_alerts.py** – Compares stress_summary.json and compare.json to regression thresholds. Loads thresholds from **experiments/config/stress_alerts.yaml** (optional; see **experiments/config/README.md**); use --config to override.
- **Schemas:** compare_report.schema.json, stress_summary.schema.json, **scale_results_ledger_row.schema.json** (ledger rows validated before append). **Fixtures:** experiments/fixtures/verify_publish_bundle/ for the verifier; experiments/fixtures/README.md.

## Experiments

- **exp-step2-lite-smoke** – First-pass SWE-bench Lite: baseline vs PF-guarded with fixed seed and budgets; policy pack `swebench_safe_v1`. Uses the deterministic slice above (20 instance_ids).

## Patch apply check (why it was failing)

The runner runs `git apply --check` on the produced patch to ensure it applies cleanly at `base_commit`. The check must run in a **clean** tree at HEAD (same as base_commit). Previously it ran in the workspace that still had the agent's uncommitted changes, so the patch failed to apply. Resetting the main workspace before the check would fix apply-check but would break replay capture, which reads final file contents from the repo. The fix: `run_patch_apply_check` uses a **temporary git worktree** at HEAD: we run `git apply --check` there and then remove the worktree. The main workspace is never mutated, so apply-check passes when the patch is valid and replay bundle capture (which runs afterward) still sees the agent's edits. The cycle script uses `--allow-empty-patch` in `validate_predictions` so validation passes when some instances have empty patches (common with OpenHands).

## When PF solve rate drops vs baseline

See **docs/internal/pf-solve-rate-debugging.md** for the full workflow: identify baseline-solved / PF-failed from `compare.csv`, extract artifacts (extract script), categorize into five buckets (categorize script), apply fixes in order (agent recovery, allowlist, budget, patch extraction), rerun and re-compare. Run/eval/compare commands for this experiment: **experiments/exp-step2-lite-smoke/commands.md**.
