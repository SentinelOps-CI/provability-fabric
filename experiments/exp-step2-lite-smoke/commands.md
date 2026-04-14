# exp-step2-lite-smoke: Commands and cases

Run from **repository root**. Paths are relative to repo root unless noted.

Before running agent-based pipeline: complete **env-checklist.md** (Docker, git, Python with `datasets` and `swebench`, OpenHands if needed, disk space). To have `pf` on PATH in WSL, see env-checklist.md "Building pf and putting it on PATH"; if `pf` is not installed, **run-baseline-pf-cycle.sh** automatically falls back to `python bench/swebench/runner.py` with the same arguments. If baseline runs produce empty patches and trajectory has only MessageEvent (no ActionEvent), see **openhands-headless-troubleshooting.md** for OpenHands-side next steps (version, model, minimal test, GUI comparison).

**See also:** Manifest schema, general eval flow, and compare overview: **experiments/README.md**. When solve rate drops vs baseline and fix-order strategy: **docs/internal/pf-solve-rate-debugging.md**. After a run, if **compare** shows low solve rates, empty patches, or gate failures, read **troubleshooting-compare-results.md** (includes **409** stale **`sweb.eval`** containers and strict compare gate signatures). To update **run-ids.md** only when all gates pass, use **experiments/scripts/update_run_ids_if_green.py** (see run-ids.md). Harness wrapper: **`experiments/scripts/run_swebench_eval.py`** supports **`--rm-stale-eval-containers`** (scoped cleanup by **`run_id`** suffix under **`sweb.eval`** names).

### Smoke run and resume

- **Smoke run (one instance):** Before a full baseline or PF run, you can validate the pipeline with a single instance by adding `--max_instances 1` to the runner (same `--out` and `--runs-dir`). This confirms workspace materialization, OpenHands, and patch emission without running all instances.
- **Early failure checks:** Phase 1.1 (check_wsl_env.py) and the pre-Phase 4.1 harness deps check (`import requests; import datasets`) in **run-baseline-pf-cycle.sh** catch broken environments (e.g. IndentationError in `requests`) before the long harness phase. If Phase 4.1 fails with a Python error in the harness, reinstall deps (e.g. `pip install --force-reinstall requests`) and re-run from Phase 1.1.
- **Resume long runs:** If a baseline or PF run is interrupted, re-run the same command with **`--skip-existing`**. The runner skips instances already present in the existing `--out` file and appends only new instance lines; existing predictions and pfmeta lines are copied so the output stays valid. Use the same `--out` and `--runs-dir` as the original run.

### Canonical entrypoint and Makefile

**One command (WSL/Linux):** From repo root, run `bash experiments/scripts/run-baseline-pf-cycle.sh` to execute the full Step-2 cycle (env check, baseline, PF, validations, harness, **replay sample** (Phase 4.2: run_replay_sample.py writes replay_summary.json), compare with gates (Phase 4.3)). Optional flags: `--update-run-ids` to run `update_run_ids_if_green.py` after compare passes (updates **experiments/exp-step2-lite-smoke/run-ids.md**, runs export_publish_artifacts, and writes publish/PUBLISH.md, **publish/GOLDEN.ok**, **publish/RESULTS.md**, **publish/VERIFY.md**, **publish/MANIFEST.sha256**, appends to scale-results-ledger.jsonl); set **`PF_REQUIRE_NONZERO_SOLVE=1`** to fail the script if both harness solve rates are still zero after a full run; `--triage` to run list_delta_cases and extract_case_bundle after compare. For the one trusted golden run and acceptance checks, see **golden-cycle.md**. When gates fail, follow **experiments/regression-loop.md**. Machine verifier: `python experiments/scripts/verify_publish_bundle.py` (see golden-cycle.md 0.4).

**Makefile (from repo root):** `make swebench-step2` runs the same script (fails on Windows with a hint to use WSL). After a successful run, use `make swebench-compare BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<run_id> PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<run_id>` to re-run compare only; use `make swebench-triage` with the same variables to list delta cases and extract case bundles; use **`make swebench-regressions`** with the same variables to run list_delta_cases, extract_case_bundle, and bucket_pf_failures_from_cases for the baseline_solved_pf_failed slice; full regression loop: **experiments/regression-loop.md**. Run IDs are in **experiments/exp-step2-lite-smoke/run-ids.md**.

### Cost comparison readiness

The full pipeline produces **cost comparison** for SWE-bench tasks: after the harness, **compare_runs.py** writes **compare.json** with **baseline.cost_per_solved** and **pf.cost_per_solved** (tokens, wall_clock_s, tool_calls, averaged over solved instances). Per-instance cost comes from `runs/<run_id>/<instance_id>/cost_report.json`; compare aggregates over instances that the harness marked resolved. You are ready to run the full pipeline when:

- **WSL or Linux** (not Windows-native).
- **Env:** `python experiments/scripts/check_wsl_env.py` passes (resource, fcntl, docker, datasets, swebench, openhands).
- **OpenHands:** Optional but recommended: `bash experiments/scripts/run_openhands_battery.sh` passes (unit + runner smoke).
- **LLM provider:** `OPENHANDS_PROVIDER` = `openai` (default), `anthropic`, or `prime_intellect` with matching keys (`OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, or `PRIME_INTELLECT_API_KEY`; for Prime, base URL is optional). See **env-checklist.md**. Model: `OPENHANDS_MODEL` or **manifest** `model.id`; cycle passes **`--openhands-model`** explicitly.
- **Docker:** `docker info` works (required for harness).
- **Experiment assets:** `experiments/exp-step2-lite-smoke/instance_ids.txt` and `manifest.json` present (20 instances for smoke).

Then run: **`bash experiments/scripts/run-baseline-pf-cycle.sh`** from repo root. On success, **runs/exp-step2-lite-smoke/compare.json** contains solve rates and cost_per_solved for baseline vs PF.

---

## Case 1: Full pipeline (baseline + PF runs, then eval, then compare)

Use this when you want to run the agent, evaluate with the SWE-bench harness, and produce the comparison report.

**Replacing recorded runs:** If existing baseline/PF run IDs are not usable (e.g. baseline was stub or PF was not guarded), run steps 1.1 and 1.2 to produce new runs, then 1.1/1.2 validation and the stub check. If any `model.patch` contains `.swebench_stub`, the run is invalid and you must stop and fix the pipeline before using the run for evaluation.

### 1.1 Baseline run (no policy)

```bash
pf bench swebench run \
  --dataset lite \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine openhands \
  --seed 42 \
  --out runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --runs-dir runs/exp-step2-lite-smoke/baseline
```
(Budgets `max_steps` and `timeout_sec` come from `experiments/exp-step2-lite-smoke/manifest.json`; override with `--openhands-max-iterations` / `--openhands-timeout` if needed.)

- Writes `runs/exp-step2-lite-smoke/baseline/predictions.jsonl` and `runs/exp-step2-lite-smoke/baseline/<run_id>/` (evidence + summary.json + cost_report per instance).
- **Note:** The runner prints `Run ID: <run_id>`. Record it for the compare step (e.g. `20260213-070743-978a35d3`).

**Immediately after the run:** Run the validation commands below (validate_predictions, then check_no_stub after both 1.1 and 1.2).

**Without pf CLI:** From repo root, run the Python runner from `bench/swebench` so imports resolve:

```bash
cd bench/swebench && python runner.py \
  --dataset lite \
  --instance-ids-file ../../experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir ../../experiments/exp-step2-lite-smoke \
  --engine openhands \
  --seed 42 \
  --out ../../runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --runs-dir ../../runs/exp-step2-lite-smoke/baseline
```
(Budgets from manifest; override with `--openhands-max-iterations` / `--openhands-timeout` if needed.)

Then validate (must pass before Docker eval). If the run was partial or failed, the runner leaves `run_status.json` in the same dir as predictions; use `--allow-partial` only when intentionally validating that partial output:

```bash
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt
```

**Hard requirement:** If any `model.patch` under the run dirs contains `.swebench_stub`, the run must be considered failed. After both baseline and PF runs, run:

```bash
python experiments/scripts/check_no_stub.py \
  runs/exp-step2-lite-smoke/baseline \
  runs/exp-step2-lite-smoke/pf
```

If this exits non-zero, do not use the run for evaluation; fix the pipeline (real OpenHands, no stub fallback) and re-run.

### 1.2 PF-guarded run (policy + sidecar)

```bash
pf bench swebench run \
  --dataset lite \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine openhands \
  --mode pf_guarded \
  --seed 42 \
  --policy swebench_safe_v1 \
  --out runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --runs-dir runs/exp-step2-lite-smoke/pf
```
(Budgets from manifest.)

- Writes `runs/exp-step2-lite-smoke/pf/predictions.jsonl` and `runs/exp-step2-lite-smoke/pf/<run_id>/` (evidence, policy_compliance_summary per instance, summary.json, cost_report).
- Record the printed **Run ID** for compare.

**Immediately after the run:** Run validate_predictions, then `validate_pf_run.py runs/exp-step2-lite-smoke/pf/<pf_run_id>`, then check_no_stub (with baseline and pf dirs).

**Without pf CLI:**

```bash
cd bench/swebench && python runner.py \
  --dataset lite \
  --instance-ids-file ../../experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir ../../experiments/exp-step2-lite-smoke \
  --engine openhands \
  --mode pf_guarded \
  --seed 42 \
  --policy swebench_safe_v1 \
  --out ../../runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --runs-dir ../../runs/exp-step2-lite-smoke/pf
```
(Budgets from manifest.)

Then validate predictions:

```bash
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt
```

Then validate PF run evidence integrity (policy hash, compliance summaries, violations consistent). Replace `<pf_run_id>` with the Run ID printed by the PF run (e.g. `20260214-163541-77bfb196`):

```bash
python bench/swebench/validate_pf_run.py runs/exp-step2-lite-smoke/pf/<pf_run_id>
```

Then run the stub check (mandatory; run is invalid if it fails):

```bash
python experiments/scripts/check_no_stub.py \
  runs/exp-step2-lite-smoke/baseline \
  runs/exp-step2-lite-smoke/pf
```

### 1.3 SWE-bench harness evaluation (both)

**Only after** baseline and PF runs (1.1, 1.2) and their validation plus stub check: run the harness, then compare. Solve rates in compare.json will remain null until the harness has been run.

SWE-bench's official evaluation harness is Docker-based and is the reference for resolved/unresolved. Use exactly the harness commands below; ensure Docker is working. Requires `swebench` and Docker. Run from repo root. **Linux/WSL only** (harness uses the Unix-only `resource` module).

```bash
# Baseline eval
python -m swebench.harness.run_evaluation \
  --predictions_path runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --dataset_name SWE-bench/SWE-bench_Lite \
  --split test \
  --run_id baseline \
  --report_dir runs/exp-step2-lite-smoke/baseline/eval

# PF eval
python -m swebench.harness.run_evaluation \
  --predictions_path runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --dataset_name SWE-bench/SWE-bench_Lite \
  --split test \
  --run_id pf \
  --report_dir runs/exp-step2-lite-smoke/pf/eval
```

Or use the wrapper (runs both; **recommended**):

```bash
python experiments/scripts/run_swebench_eval.py \
  --baseline-predictions runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --pf-predictions runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval
```

**Harness reliability (WSL/Docker under load):** The wrapper accepts **`--max-workers N`** (default 4) and **`--timeout SECONDS`** (default 1800 per instance). On hosts that show many harness errors (e.g. WSL `accept4 failed 110`), try **`--max-workers 1`** or **`2`** before changing code. The wrapper retries a failed harness subprocess **once** (two attempts total). Set **`HF_TOKEN`** in the environment (see **env-checklist.md**) to reduce Hugging Face Hub rate-limit warnings when loading the dataset.

- The wrapper tries dataset IDs in order (`SWE-bench/SWE-bench_Lite`, then `princeton-nlp/SWE-bench_Lite`) and uses the first that loads. The chosen ID is written to **`runs/exp-step2-lite-smoke/harness_dataset_id.txt`** so future runs and compare use the same dataset without manual choice.
- Writes harness run reports and per-instance logs under `.../baseline/eval` and `.../pf/eval` (and possibly `evaluation_logs/` under those dirs). After each harness run the wrapper writes **`eval_metadata.json`** in that eval dir with the run_id (from run_status.json next to the predictions file), predictions_sha256 (if the runner wrote predictions.sha256), dataset_name, split, and datasets/swebench versions. Compare with `--require-harness` uses this to assert that the eval dir matches the run that produced the predictions (run_id and optional hash); a wrong pairing fails with a clear error.

Then run compare (use the Run IDs printed in steps 1.1 and 1.2). Use `--require-harness` so compare fails fast if eval reports are missing or solve rates are null; use `--require-compliance` so it fails if any PF instance is missing `policy_compliance_summary.json`:

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<NEW_BASELINE_RUN_ID> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<NEW_PF_RUN_ID> \
  --require-harness --require-compliance --require-patch-apply --require-priced-models
```

**Acceptance gate:** `runs/exp-step2-lite-smoke/compare.json` must have numeric solve rates (not null): `baseline.solve_rate` and `pf.solve_rate` must be numbers. If they are null, the harness (1.3) has not been run or its reports are missing under `baseline/eval` and `pf/eval`. With `--require-harness`, compare exits with an error instead of writing nulls.

**Patch-apply gate (Step 2 parity):** `compare.json` includes `patch_apply.total`, `patch_apply.applies_true`, `patch_apply.applies_false`, `patch_apply.errors_topN` (stderr bucketed), and **empty_patch_reasons_topN** (counts per reason: agent_no_changes, patch_too_large, diff_timeout, apply_check_failed, workspace_missing_or_failed, guard_denial_prevented_writes). For Step 2 parity runs, **patch_apply.applies_false** must be 0. If not zero, fix patch extraction or apply logic before interpreting solve rates. Use `--require-patch-apply` to make compare exit with error when applies_false != 0.

**When using --require-harness**, compare also: (1) **Stale-eval check:** fails if the predictions file is newer than the eval report (re-run harness before compare). (2) **predictions_sha256:** if present, must match eval_metadata so eval was run on the same predictions. (3) **Budget drift:** if both run dirs have experiment_manifest.json, timeout_sec, max_steps, max_tool_calls, model, model_params must match; drift fails the run. Compare merges **replay** from replay_summary.json (when run_replay_sample.py was run) and adds **policy** (reason_codes_topN, denied_commands_topN) from PF compliance.

Then collect pass/fail and failure buckets (optional):

```bash
python experiments/scripts/collect_eval_results.py \
  runs/exp-step2-lite-smoke/baseline/eval \
  runs/exp-step2-lite-smoke/pf/eval
```

Use `--csv out.csv` for a per-instance CSV (instance_id, run_label, status); use `--json` for machine-readable summary.

### 1.4 Comparison report (reference)

The compare command is run in step 1.3 (immediately after the harness). **Outputs:** `runs/exp-step2-lite-smoke/compare.json` and `runs/exp-step2-lite-smoke/compare.csv`.

**Acceptance checks (must be true before moving on):**

1. `runs/exp-step2-lite-smoke/compare.csv` exists.
2. `compare.csv` has 20 instance rows plus one `_summary` row (21 data rows + header = 22 lines).
3. **Solve rates non-null:** `compare.json` contains numeric `baseline.solve_rate` and `pf.solve_rate` (not null). If either is null, re-run the harness (1.3) and ensure reports exist under `baseline/eval` and `pf/eval`, then run compare again.

---

## Parity gate (Step 2 completion)

Define a **hard gate** for Step 2 completion on the 20-instance slice:

- **Parity:** `pf.solve_rate >= baseline.solve_rate - 0.01`

`pf.policy_violation_rate_final > 0` is allowed (even desirable), but violations must be:

- Correctly classified (`reason_codes` meaningful),
- Reproducible across replays,
- Not caused by false positives in path parsing.

Check the gate after compare: read `compare.json`; if `baseline.solve_rate` and `pf.solve_rate` are set, pass when `pf.solve_rate >= baseline.solve_rate - 0.01`. The export script (see below) can write `parity_gate_passed` into the publish metadata.

---

## Publishable artifacts (SWE-bench-style)

The SWE-bench community standard for publishing runs is: predictions + metadata + logs/trajectories. Export a submission-style folder for credibility:

```
runs/exp-step2-lite-smoke/publish/
  metadata.yaml      # run ids, solve rates, parity_gate_passed, policy_violation_rate_final
  all_preds.jsonl   # PF predictions (one JSON object per line)
  logs/<instance_id>/...   # PF evidence bundle + harness logs per instance
  trajs/<instance_id>.json   # engine_trace.json per instance
```

When you run the canonical script with **`--update-run-ids`**, `update_run_ids_if_green.py` runs export and writes **`publish/PUBLISH.md`** (run ids, solve rates, policy violation rate, replay success rate, env drift) automatically after updating run-ids.md. To generate the publish folder manually after compare:

```bash
python experiments/scripts/export_publish_artifacts.py \
  --pf-predictions runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval \
  --compare-json runs/exp-step2-lite-smoke/compare.json \
  --out-dir runs/exp-step2-lite-smoke/publish \
  --experiment-id exp-step2-lite-smoke \
  --baseline-run-id <baseline_run_id> \
  --pf-run-id <pf_run_id>
```

Replace `<pf_run_id>` and `<baseline_run_id>` with your run IDs. This produces the layout above so the run "looks like a real evaluation artifact," not a blog demo.

---

## Analysis: delta lists and per-instance debug bundles

After compare, list instance IDs by delta category and extract per-instance debug bundles (evidence + eval logs + traces):

```bash
# 1. List delta categories (from compare.csv)
python experiments/scripts/list_delta_cases.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --out-dir runs/exp-step2-lite-smoke/analysis

# 2. Extract per-instance bundles for e.g. baseline-solved / PF-failed
python experiments/scripts/extract_case_bundle.py \
  --instance-ids-file runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval \
  --out-dir runs/exp-step2-lite-smoke/analysis/cases
```

**Acceptance check for case bundles:** For each `runs/exp-step2-lite-smoke/analysis/cases/<id>/pf/` you should see at least:

- `model.patch`
- `engine_trace.json` (or whatever the runner writes)
- `policy_compliance_summary.json` (PF only; guarded mode)

**3. Automatic bucketing (policy vs budget vs patch-format vs agent quality):**

```bash
python experiments/scripts/bucket_pf_failures_from_cases.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --cases-dir runs/exp-step2-lite-smoke/analysis/cases \
  --out-csv runs/exp-step2-lite-smoke/analysis/pf_failure_buckets.csv
```

Produces `pf_failure_buckets.csv` with one row per instance: `instance_id`, `bucket` (e.g. `policy_denial_or_violation`, `empty_patch_or_patch_write_failed`, `budget_timeout`, `patch_format_or_apply`, `agent_quality_or_missing_tooling`, `needs_manual_read`), `pf_status`, `baseline_status`, `violations`, `reason_codes`, `notes`. For harness-based categorization into the five fix-strategy buckets (policy_too_strict, agent_not_adapting, etc.), use `experiments/scripts/categorize_pf_failures.py` with `--experiment-dir` and `--pf-run-dir`.

---

## Rerun only the regression slice and re-evaluate

After implementing a fix, rerun only the instance IDs in `baseline_solved_pf_failed.txt` (PF-guarded), then run the harness on the rerun and compare against the same baseline. Run from repo root.

**1. PF rerun (regression slice only):**

```bash
pf bench swebench run \
  --dataset lite \
  --instance-ids-file runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine openhands \
  --mode pf_guarded \
  --seed 42 \
  --policy swebench_safe_v1 \
  --out runs/exp-step2-lite-smoke/pf_rerun/predictions.jsonl \
  --runs-dir runs/exp-step2-lite-smoke/pf_rerun
```

Record the printed **Run ID** (e.g. `<NEW_RUN_ID>`) for the compare step.

**2. Harness eval (pf_rerun only):**

```bash
python -m swebench.harness.run_evaluation \
  --predictions_path runs/exp-step2-lite-smoke/pf_rerun/predictions.jsonl \
  --dataset_name SWE-bench/SWE-bench_Lite \
  --split test \
  --run_id pf_rerun \
  --report_dir runs/exp-step2-lite-smoke/pf_rerun/eval
```

**3. Compare against the same baseline:**

Use the same strict flags on every compare so you cannot "think you improved" without harness, compliance, and patch-apply all passing:

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf_rerun/<NEW_RUN_ID> \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf_rerun/eval \
  --require-harness --require-compliance --require-patch-apply --require-priced-models
```

Replace `<baseline_run_id>` with your original baseline run ID (e.g. `20260213-152958-003a3ba1`) and `<NEW_RUN_ID>` with the run ID from step 1. `--pf-eval-dir` is required so compare reads solve rate from the rerun eval, not from `pf/eval`.

**Operational rules for the regression-slice loop:** Always compare to the same baseline run ID; keep seed, budgets, and policy pinned; re-use the exact compare flags (`--require-harness`, `--require-compliance`, `--require-patch-apply`, `--require-priced-models`) for every iteration (same as **`make swebench-compare`** and **`run-baseline-pf-cycle.sh`** Phase 4.3).

---

## Case 2: You already have predictions; only run eval + compare

If `runs/exp-step2-lite-smoke/baseline/predictions.jsonl` and `runs/exp-step2-lite-smoke/pf/predictions.jsonl` exist and you already have run dirs with evidence:

1. Run harness (Case 1.3) to populate `baseline/eval` and `pf/eval`.
2. Run compare (Case 1.4) with the correct `--baseline-run-dir` and `--pf-run-dir`.

---

## Case 3: You have run dirs but no harness eval yet

If you have baseline and PF run dirs (with summary.json and cost_report / policy_compliance_summary) but have not run the SWE-bench harness:

- Run compare anyway. It will still produce:
  - **baseline.cost_per_solved** and **pf.cost_per_solved** (from run dirs).
  - **pf.policy_violation_rate_*** and **violation_reasons_top10** (from PF run dir).
  - **baseline.solve_rate** and **pf.solve_rate** will be null until harness reports exist in `baseline/eval` and `pf/eval`.

---

## Case 4: Only baseline (or only PF) run exists

- Omit the missing run dir: e.g. only `--baseline-run-dir` or only `--pf-run-dir`.
- Solve rates still come from eval dirs if present; cost and compliance only for the run dir(s) you pass.

---

## Case 5: Override paths

- `--experiment-dir` defaults to `runs/exp-step2-lite-smoke`; eval dirs default to `<experiment-dir>/baseline/eval` and `<experiment-dir>/pf/eval`.
- Override with `--baseline-eval-dir`, `--pf-eval-dir`.
- Output dir for compare.json/compare.csv defaults to `--experiment-dir`; override with `--out`.

Example with custom output dir:

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/20260213-070743-978a35d3 \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/20260213-120000-abc123 \
  --out runs/exp-step2-lite-smoke
```

---

## Collecting eval results (optional)

After harness runs, per-instance pass/fail and failure buckets:

```bash
python experiments/scripts/collect_eval_results.py \
  runs/exp-step2-lite-smoke/baseline/eval \
  runs/exp-step2-lite-smoke/pf/eval
```

Use `--csv out.csv` for a pivot-friendly CSV of instance_id, run_label, status.

---

## Running when you need to shut down (remote or resume)

Runs take a long time (many minutes to hours). Two practical options:

**Option A: Run on a remote machine (recommended if you shut down your laptop often)**  
Run the same pipeline on a machine that stays on: a Linux server you SSH into, or a cloud VM (e.g. GCP, AWS, Azure). Clone the repo there, install dependencies (Docker, Python, venv, `datasets`, `swebench`, OpenHands), copy or set `.env` (API keys), then run from repo root:

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh
```

Use `screen` or `tmux` on the remote host so the run continues if your SSH session drops (e.g. `tmux new -s swebench` then run the script; detach with Ctrl+B D; reattach later with `tmux attach -t swebench`). Shutting down your **local** computer does not stop the remote process.

**Option B: Run in chunks locally with resume**  
If you run locally and must shut down, you can **resume** the baseline and PF runs later. Run the **runner** commands manually (not the full cycle script) so you can re-run them with `--skip-existing` after an interrupt.

1. **Baseline run (start or resume).** From repo root, same `--out` and `--runs-dir` every time; add `--skip-existing` when resuming:

   ```bash
   python bench/swebench/runner.py \
     --dataset Lite \
     --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
     --experiment-dir experiments/exp-step2-lite-smoke \
     --engine openhands \
     --seed 42 \
     --out runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
     --runs-dir runs/exp-step2-lite-smoke/baseline
   ```

   If interrupted, re-run the **exact same command** with `--skip-existing` appended. Repeat until the run completes (runner prints "Run ID:" and exits normally).

2. **PF run (start or resume).** Same idea; add `--skip-existing` when resuming:

   ```bash
   python bench/swebench/runner.py \
     --dataset Lite \
     --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
     --experiment-dir experiments/exp-step2-lite-smoke \
     --engine openhands \
     --mode pf_guarded \
     --seed 42 \
     --policy swebench_safe_v1 \
     --out runs/exp-step2-lite-smoke/pf/predictions.jsonl \
     --runs-dir runs/exp-step2-lite-smoke/pf
   ```

   Resume after interrupt by re-running with `--skip-existing`.

3. **After both runs are complete**, run the rest of the cycle once: validation, harness, compare. From repo root (replace `<BASELINE_RUN_ID>` and `<PF_RUN_ID>` with the printed Run IDs):

   ```bash
   python experiments/scripts/validate_predictions.py runs/exp-step2-lite-smoke/baseline/predictions.jsonl -n 20 --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt --allow-empty-patch
   python experiments/scripts/validate_predictions.py runs/exp-step2-lite-smoke/pf/predictions.jsonl -n 20 --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt --allow-empty-patch
   python bench/swebench/validate_pf_run.py runs/exp-step2-lite-smoke/pf/<PF_RUN_ID>
   python experiments/scripts/check_no_stub.py runs/exp-step2-lite-smoke/baseline runs/exp-step2-lite-smoke/pf
   python experiments/scripts/run_swebench_eval.py --baseline-predictions runs/exp-step2-lite-smoke/baseline/predictions.jsonl --pf-predictions runs/exp-step2-lite-smoke/pf/predictions.jsonl --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval
   python experiments/scripts/compare_runs.py --experiment-dir runs/exp-step2-lite-smoke --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<BASELINE_RUN_ID> --pf-run-dir runs/exp-step2-lite-smoke/pf/<PF_RUN_ID> --require-harness --require-compliance --require-patch-apply --require-priced-models
   ```

**Quick smoke before a long run:** From repo root, run one instance to confirm env and OpenHands work, then start the full run (or remote/chunked run):

```bash
cd bench/swebench && python runner.py --dataset Lite --instance-ids-file ../../experiments/exp-step2-lite-smoke/instance_ids.txt --experiment-dir ../../experiments/exp-step2-lite-smoke --engine openhands --seed 42 --max_instances 1 --out ../../runs/exp-step2-lite-smoke/baseline/predictions.jsonl --runs-dir ../../runs/exp-step2-lite-smoke/baseline
```

---

## Troubleshooting: Phase 4.1 (harness) and PF run failures

- **Phase 4.1 fails with `IndentationError` in `requests/models.py`:** The installed `requests` package in your venv may be corrupted or partially edited. Fix: reinstall from PyPI: `pip install --force-reinstall requests`. Then re-run the cycle or run Phase 4.1 (harness) manually.
- **Phase 4.1 fails with `500 Server Error` for `localhost/version`:** WSL cannot reach the Docker daemon. Start Docker Desktop on Windows, wait until it is fully running, and in Docker Desktop settings ensure **Use the WSL 2 based engine** and **Enable integration with my default WSL distro** (or your distro) are on. Then run `docker info` in WSL; if that works, re-run Phase 4.1.
- **`docker info` in WSL segfaults:** The Docker CLI or daemon bridge is crashing. Update Docker Desktop and run `wsl --update` in Windows PowerShell, then restart WSL. Ensure WSL is using Docker Desktop's CLI (Docker Desktop settings: enable WSL integration for your distro). If it still segfaults, use **Docker WSL stable setup** below or run the harness on a native Linux host or VM.

### Docker WSL stable setup (native Linux Engine inside WSL)

When Docker Desktop integration segfaults or returns persistent `500` errors, run the **Linux Docker Engine** (`dockerd`, `containerd`) directly inside your WSL distro so the harness talks to a local daemon without the Desktop bridge.

1. **Detect failure:** `docker info` exits non-zero, segfaults, or Python reports `APIError: 500` for `localhost/version`.
2. **Install (Ubuntu WSL):** Install `docker.io` and `containerd` from distro packages, or follow Docker's docs for static binaries. Ensure `dockerd` and `containerd` are available.
3. **Isolated data root (avoid Desktop conflicts):** Use a data directory under `/tmp` or a dedicated path, e.g. `/tmp/docker-wsl-root`, and a Unix socket such as `/tmp/docker-wsl.sock`. Example (adjust paths; run as root or with sudo):
   - Start `containerd` with `--root /tmp/containerd-wsl-root`.
   - Start `dockerd` with `--data-root /tmp/docker-wsl-root --host unix:///tmp/docker-wsl.sock`.
4. **Client:** Point the CLI at the socket: `export DOCKER_HOST=unix:///tmp/docker-wsl.sock`. Add that line to repo-root `.env` (sourced by `run-baseline-pf-cycle.sh`) so harness subprocesses use the same daemon.
5. **Verify:** `docker info` and `docker pull hello-world` under that `DOCKER_HOST`. Optional full check: `python experiments/scripts/check_wsl_env.py --docker-pull`.

Stop native `dockerd` when you return to Docker Desktop to avoid port/socket confusion.

- **Phase 4.1 fails with `500 Server Error` for `images/json` (Docker cleanup):** The harness runs all instances then cleans Docker images; the daemon can return 500 under load. The wrapper retries once. If it still fails, restart Docker Desktop, then re-run Phase 4.1 only (same `run_swebench_eval.py` arguments). Baseline and PF runs are unchanged; you do not need to re-run baseline or PF.
- **PF run: instances show `returncode=1`, `trajectory: 0 events`, `stderr_len=5497`:** OpenHands subprocess exited with an error (e.g. guard interaction, env, or API). The runner writes a tail of OpenHands stderr to **`runs/<run_id>/<instance_id>/openhands_stderr_tail.txt`** when the run fails or has 0 events with non-empty stderr; use that for quick debugging. The full stderr is also in `workspaces/<instance_id>/scratch/openhands_stderr.txt` when the engine wrote it. If many instances fail after the first few, possible causes include rate limiting, guard blocking required setup, or a crash in OpenHands under the guarded environment.

---

## Quick compare (no harness)

If you have at least one run dir (baseline or PF) but have not run the SWE-bench harness:

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/20260213-070743-978a35d3
```

- Eval dirs (`baseline/eval`, `pf/eval`) may be missing; the script skips them and does not fail.
- **compare.json** will have `solve_rate` and `delta.solve_rate` as null when harness reports are missing; baseline/pf **cost_per_solved** are filled only when harness reports exist. **patch_apply** aggregates `patch_apply_check.json` per instance: `total`, `applies_true`, `applies_false`, `errors_topN` (stderr bucketed); **empty_patch_reasons_topN** lists reason codes and counts. When eval_metadata exists, compare also emits **reproducibility** fields (dataset_name, split, datasets_version, swebench_version, harness_dataset_id, openhands_version). Use **--require-harness** to exit with error unless both eval reports exist, yield non-null solve rates, and run_id matches (run_status, run_dir name, eval_metadata); **--require-compliance** unless every PF instance has `policy_compliance_summary.json`; **--require-patch-apply** unless `patch_apply.applies_false == 0`.
- **compare.csv** will have one row per instance (including **baseline_patch_applies** and **pf_patch_applies** when run dirs are given) plus a `_summary` row with patch_apply totals.
- **run-ids.md:** Update only after all gates pass. The canonical way is to run `python experiments/scripts/update_run_ids_if_green.py --experiment-dir runs/exp-step2-lite-smoke --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<run_id> --pf-run-dir runs/exp-step2-lite-smoke/pf/<run_id>` (optionally with `--instance-ids-file`, `--expected-count`, and **`--allow-empty-patch`** when some instances have empty patches). The **cycle script** (`run-baseline-pf-cycle.sh --update-run-ids`) invokes this with `--allow-empty-patch` so runs with some empty-patch instances can still update run-ids. See **run-ids.md** in this directory.
