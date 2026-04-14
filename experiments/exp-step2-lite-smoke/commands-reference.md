# SWE-bench: Full command reference (implementation, testing, results)

All commands assume **repository root** unless noted. Real agent runs and harness require **WSL or Linux**; unit/smoke tests and local verification run on any OS.

---

## 1. Environment setup (WSL/Linux, one-time)

### 1.1 Build PF CLI and put on PATH (optional; script can fall back to Python runner)

```bash
go build -o ~/.local/bin/pf ./core/cli/pf
echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc && source ~/.bashrc
which pf && pf bench swebench run --help
```

### 1.2 Python dependencies

```bash
pip install datasets swebench openhands
```

(For reproducibility, pin versions: `pip install datasets==X.Y.Z swebench==A.B.C openhands==...`; see bench/swebench/README.md "Reproducibility".)

### 1.3 Environment check (must pass before runs)

```bash
python experiments/scripts/check_wsl_env.py
```

Or manually:

```bash
python -c "import resource; print('resource ok')"
python -c "import fcntl; print('fcntl ok')"
docker info
python -c "import datasets, swebench; print('datasets+swebench ok')"
python -c "import openhands; print('openhands ok')"
```

### 1.4 Credentials (API keys for OpenHands)

Create `.env` in repo root with `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, and optionally `OPENHANDS_API_KEY`, `OPENAI_BASE_URL`; or export before running.

### 1.5 Preflight (optional; materialize workspaces, no agent)

```bash
pf bench swebench run --dataset Lite --split test --max_instances 5 --preflight
```

---

## 2. Testing (no WSL required)

### 2.1 Runner smoke (mock engine, no network)

```bash
pytest tests/test_swebench_runner_smoke.py -q --tb=short
```

### 2.2 Full bench/experiments unit suite (CI-equivalent)

```bash
pytest tests/test_experiments_compare_runs.py tests/test_validate_predictions.py tests/test_check_no_stub.py tests/test_validate_pf_run.py tests/test_loader_from_file.py tests/test_workspace_plan.py tests/test_replay_roundtrip.py tests/test_swebench_runner_smoke.py tests/test_openhands_engine.py tests/test_policy_loader.py tests/test_cost_report.py tests/test_proof_hook.py tests/test_check_wsl_env.py tests/test_fill_manifest_from_run.py tests/test_list_delta_cases.py tests/test_bucket_pf_failures.py tests/test_policy_guard_deny_allow.py tests/test_summarize_stress_run.py -v
```

### 2.3 Local verification (verifier, ledger append, stress checks; no WSL)

```bash
python experiments/scripts/run_verification_tests.py
```

### 2.4 Verify publish bundle on fixture (no real run)

```bash
python experiments/scripts/verify_publish_bundle.py --publish-dir experiments/fixtures/verify_publish_bundle/publish --compare-json experiments/fixtures/verify_publish_bundle/compare.json --skip-run-dir-check
```

---

## 3. Full pipeline: one-shot (WSL/Linux)

Single script runs env check, manifest fill, baseline run, PF run, validations, harness, replay sample, compare with gates.

### 3.1 Full cycle (no RUN_IDS update)

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh
```

### 3.2 Full cycle + update RUN_IDS and publish bundle when gates pass

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids
```

### 3.3 Full cycle + update RUN_IDS + triage (delta lists and case bundles)

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids --triage
```

### 3.4 Makefile shortcut (fails on Windows with hint to use WSL)

```bash
make swebench-step2
```

---

## 4. Full pipeline: manual steps (WSL/Linux)

Use when you need to run baseline and PF separately or re-run only some steps. Replace `<baseline_run_id>` and `<pf_run_id>` with the Run IDs printed by the runner.

### 4.1 Fill manifest (optional; do before or after runs)

```bash
python experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json
```

### 4.2 Baseline run

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

Record the printed **Run ID**.

### 4.3 Validate baseline predictions

```bash
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt
```

### 4.4 PF-guarded run

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

Record the printed **Run ID**.

### 4.5 Validate PF predictions and PF run evidence

```bash
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt

python bench/swebench/validate_pf_run.py runs/exp-step2-lite-smoke/pf/<pf_run_id>
```

### 4.6 Stub check (mandatory; run invalid if this fails)

```bash
python experiments/scripts/check_no_stub.py \
  runs/exp-step2-lite-smoke/baseline \
  runs/exp-step2-lite-smoke/pf
```

### 4.7 Harness evaluation (baseline + PF)

```bash
python experiments/scripts/run_swebench_eval.py \
  --baseline-predictions runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --pf-predictions runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval
```

### 4.8 Compare (with gates)

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --require-harness --require-compliance --require-patch-apply
```

Outputs: `runs/exp-step2-lite-smoke/compare.json`, `runs/exp-step2-lite-smoke/compare.csv`.

### 4.9 Replay sample (optional; enriches compare with replay section)

Run after compare; uses compare.json and PF run dir. Then re-run compare to merge replay_summary.json.

```bash
python experiments/scripts/run_replay_sample.py \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --compare-json runs/exp-step2-lite-smoke/compare.json
```

Then run compare again (same command as 4.8) so the report includes the replay section.

### 4.10 Update RUN_IDS and publish bundle (only when all gates pass)

```bash
python experiments/scripts/update_run_ids_if_green.py \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id>
```

When gates pass: updates `experiments/exp-step2-lite-smoke/run-ids.md`, runs export, writes publish/PUBLISH.md, GOLDEN.ok, RESULTS.md, VERIFY.md, appends to scale-results-ledger.jsonl.

---

## 5. Results and analysis

### 5.1 Collect pass/fail summary (optional)

```bash
python experiments/scripts/collect_eval_results.py \
  runs/exp-step2-lite-smoke/baseline/eval \
  runs/exp-step2-lite-smoke/pf/eval
```

Use `--csv out.csv` for per-instance CSV; `--json` for machine-readable summary.

### 5.2 Delta lists and case bundles (after compare)

```bash
python experiments/scripts/list_delta_cases.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --out-dir runs/exp-step2-lite-smoke/analysis

python experiments/scripts/extract_case_bundle.py \
  --instance-ids-file runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval \
  --out-dir runs/exp-step2-lite-smoke/analysis/cases
```

### 5.3 Regression loop (baseline_solved_pf_failed slice: list, extract, bucket)

Requires `BASELINE_RUN_DIR` and `PF_RUN_DIR` from run-ids.md:

```bash
make swebench-regressions BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<run_id> PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<run_id>
```

Or run the underlying scripts (see experiments/regression-loop.md).

### 5.4 Re-run compare only (after harness or replay changes)

```bash
make swebench-compare BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<run_id> PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<run_id>
```

### 5.5 Re-run triage only

```bash
make swebench-triage BASELINE_RUN_DIR=runs/exp-step2-lite-smoke/baseline/<run_id> PF_RUN_DIR=runs/exp-step2-lite-smoke/pf/<run_id>
```

---

## 6. Golden run verification

After a successful run with `--update-run-ids`, verify the publish bundle:

```bash
python experiments/scripts/verify_publish_bundle.py \
  --publish-dir runs/exp-step2-lite-smoke/publish \
  --compare-json runs/exp-step2-lite-smoke/compare.json \
  --run-ids-md experiments/exp-step2-lite-smoke/run-ids.md
```

---

## 7. Key artifacts

| Artifact | Path |
|----------|------|
| Baseline predictions | `runs/exp-step2-lite-smoke/baseline/predictions.jsonl` |
| PF predictions | `runs/exp-step2-lite-smoke/pf/predictions.jsonl` |
| Compare report | `runs/exp-step2-lite-smoke/compare.json`, `compare.csv` |
| RUN_IDS | `experiments/exp-step2-lite-smoke/run-ids.md` |
| Publish bundle | `runs/exp-step2-lite-smoke/publish/` (GOLDEN.ok, PUBLISH.md, RESULTS.md, VERIFY.md, metadata.yaml, all_preds.jsonl, logs/, trajs/) |
| Scale ledger | `experiments/scale-results-ledger.jsonl` |

---

## 8. Without pf CLI

If `pf` is not on PATH, use the Python runner from `bench/swebench` (see commands.md Case 1.1 and 1.2 for full args with `../../` paths). The one-shot script `run-baseline-pf-cycle.sh` automatically falls back to `python bench/swebench/runner.py` when `pf` is not found.

---

See **commands.md** for detailed cases and **golden-cycle.md** for the golden run and acceptance checks. When gates fail, follow **experiments/regression-loop.md**.
