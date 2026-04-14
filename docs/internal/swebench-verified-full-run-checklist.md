# SWE-bench Verified full run checklist

Use this before starting a full **Verified** sweep (`princeton-nlp/SWE-bench_Verified`, typically 500 test instances).

## 1. Environment

- **Unix-like OS (Linux or WSL)** for `--engine openhands`. Native Windows is blocked by runner validation for OpenHands (use `--engine mock` only for CI-style smoke on Windows).
- **Python** with `datasets`, `swebench`, and project dependencies installed.
- **Git** on `PATH` and network access to clone GitHub repos.
- **Hugging Face**: optional `HF_TOKEN` for higher rate limits when downloading the dataset.
- **LLM**: set `OPENHANDS_PROVIDER` and the matching API key env (`OPENAI_API_KEY`, `PRIME_INTELLECT_API_KEY`, etc.) and `OPENHANDS_MODEL` as needed.

## 2. Automated checks (repo root)

Run the same unit tests as CI (see `.github/workflows/bench-swebench-unit.yaml`), including OpenHands/provider tests:

```bash
pytest tests/test_experiments_compare_runs.py tests/test_validate_predictions.py tests/test_check_no_stub.py tests/test_validate_pf_run.py tests/test_loader_from_file.py tests/test_workspace_plan.py tests/test_replay_roundtrip.py tests/test_swebench_runner_smoke.py tests/test_openhands_engine.py tests/test_policy_loader.py tests/test_cost_report.py tests/test_proof_hook.py tests/test_check_wsl_env.py tests/test_fill_manifest_from_run.py tests/test_list_delta_cases.py tests/test_bucket_pf_failures.py tests/test_policy_guard_deny_allow.py tests/test_provider_env.py tests/test_openhands_provider_env.py tests/test_run_swebench_eval_cleanup.py tests/test_run_config.py tests/test_openhands_task_compaction.py tests/test_openhands_timeout_accounting.py tests/test_prime_proxy_normalization.py -q
```

## 3. Verified preflight (no agent)

Materialize workspaces and quick git stats for a small slice of Verified (no API calls to the model):

**On Windows** (validation allows mock engine only):

```bash
python bench/swebench/runner.py --dataset Verified --split test --max_instances 5 --preflight --workspaces-dir workspaces_verify_preflight_smoke --engine mock
```

**On Linux/WSL** (same command without `--engine mock` is fine; default is `openhands` but preflight exits before the agent).

Inspect stderr: every instance should complete materialization; occasional clone/network issues may show in the `note` column—retry or fix network before a multi-day run.

## 4. Pilot agent run (Linux/WSL)

Before the full Verified job, run a **small** OpenHands slice (e.g. `--max_instances 3`) with production-like timeouts and your chosen model. Confirm non-empty patches where expected and review `runs/<run_id>/env.json` and `engine_trace.json`.

## 5. Operational gate (optional, Linux/WSL)

After keys are set:

```bash
python experiments/scripts/openhands_regression_gate.py --timeout 180 --max-iterations 2
```

Requires `openhands` on `PATH` and valid LLM credentials. See `docs/internal/openhands-compatibility-matrix.md`.

## 6. Full Verified command shape (Linux/WSL)

```bash
python bench/swebench/runner.py \
  --dataset Verified \
  --split test \
  --out predictions-verified.jsonl \
  --runs-dir runs \
  --engine openhands \
  --openhands-timeout <seconds> \
  --openhands-max-iterations <n>
```

Omit `--max_instances` for all instances. Use `--skip-existing` and a stable `--out` to resume.

## 7. After predictions

Run harness/eval and compare flows per your experiment docs; ensure Docker and disk space for eval containers.
