# SWE-bench Prime stabilization: regression matrix

This document records how to verify the SWE-bench baseline/PF pipeline after provider routing, eval cleanup, compare gates, and shared `provider_env` changes. Run from repository root unless noted.

## 1. Fast automated gate (required)

The same modules are run in **CI** (`.github/workflows/bench-swebench-unit.yaml`) on Ubuntu and Windows together with the other bench/experiments unit tests.

```bash
python -m pytest \
  tests/test_provider_env.py \
  tests/test_openhands_provider_env.py \
  tests/test_run_swebench_eval_cleanup.py \
  tests/test_experiments_compare_runs.py \
  tests/test_run_config.py \
  -v --tb=short
```

**Evidence:** all tests pass (includes strict compare on healthy fixture, docker cleanup selection, provider credentials matrix, `openhands_timeout == 1200` default).

## 2. Budget and task-shape drift (static)

| Source | Field | Expected |
|--------|--------|----------|
| [bench/swebench/run_config.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/run_config.py) | `RunConfig.openhands_timeout` default | `1200` |
| [experiments/exp-step2-lite-smoke/manifest.json](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/exp-step2-lite-smoke/manifest.json) | `budgets.timeout_sec` | `1200` |
| [experiments/scripts/run-baseline-pf-cycle.sh](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/scripts/run-baseline-pf-cycle.sh) | `OPENHANDS_TIMEOUT` default | `1200` |
| Engine | `PF_OPENHANDS_MAX_TASK_CHARS` default | `12000` (see [bench/swebench/engines/openhands_engine.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/engines/openhands_engine.py)) |

## 3. Provider / subprocess contract (code review checklist)

- [bench/swebench/provider_env.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/provider_env.py): single normalization for provider, keys, base URL, model prefix for Prime.
- [bench/swebench/runner.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/runner.py): `env.json` uses `llm_env_diagnostics()` when available; fallback uses `normalize_openhands_provider`.
- [experiments/scripts/ensure_openhands_config.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/scripts/ensure_openhands_config.py): uses `llm_credentials` and `effective_llm_model`.
- [bench/swebench/engines/openhands_engine.py](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/engines/openhands_engine.py):
  - `prime_intellect` uses subprocess path with Prime compat proxy when configured.
  - Subprocess `env` forwards `OPENHANDS_PROVIDER`, `OPENHANDS_MODEL`, `PRIME_TEAM_ID`, and sets `OPENHANDS_PROVIDER` to the **normalized** provider string.
  - Authentication errors: if `pit_*` appears in env or error text, remediation points to Prime routing and `env.json`, not only OpenAI keys.

## 4. Prime smoke (WSL/Linux, requires credentials)

Run one instance with Prime (no custom base URL) to confirm routing metadata:

```bash
export OPENHANDS_PROVIDER=prime_intellect
export PRIME_INTELLECT_API_KEY="your-pit-key"
# Unset custom bases for this check:
unset PRIME_INTELLECT_BASE_URL OPENAI_BASE_URL

pf bench swebench run \
  --dataset lite \
  --max_instances 1 \
  --instance_ids astropy__astropy-12907 \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine openhands \
  --out runs/_smoke-prime/predictions.jsonl \
  --runs-dir runs/_smoke-prime
```

**Assert** in `runs/_smoke-prime/<run_id>/env.json`:

- `openhands_provider` is `prime_intellect`
- `llm_base_url_source` is `DEFAULT_PRIME_INTELLECT_INFERENCE_BASE_URL`
- `llm_base_url_effective` contains `pinference`

**Assert** in stderr: preflight line mentions Prime when key is set; on auth failure, logs do not exclusively tell you to set `OPENAI_API_KEY` when `pit_*` / Prime routing applies.

## 5. Eval stale-container cleanup (Docker)

Automated: `tests/test_run_swebench_eval_cleanup.py` (mocked `docker`).

Manual after a harness crash:

```bash
docker ps -a --filter name=sweb.eval --format '{{.ID}}\t{{.Names}}'
```

Only names whose final `.`-separated segment equals your harness `run_id` should be removed by `run_swebench_eval.py --rm-stale-eval-containers`.

## 6. Compare strict gates (healthy runpair)

Automated: `test_compare_runs_all_strict_flags_pass_on_healthy_fixture`.

Manual on real runs:

```bash
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<baseline_run_id> \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --require-harness \
  --require-compliance \
  --require-patch-apply \
  --require-priced-models
```

Expect exit code 0 and `compare.json`, `compare.csv`, `metrics_full.json` under the experiment dir.

## 7. Runbook consistency

Cross-check failure signatures and recovery steps in:

- [bench/swebench/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/README.md)
- [experiments/exp-step2-lite-smoke/env-checklist.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/exp-step2-lite-smoke/env-checklist.md)
- [experiments/exp-step2-lite-smoke/commands.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/exp-step2-lite-smoke/commands.md)
- [experiments/exp-step2-lite-smoke/troubleshooting-compare-results.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/exp-step2-lite-smoke/troubleshooting-compare-results.md)

## Provider matrix (manual or scripted)

| OPENHANDS_PROVIDER | Required secret | Base URL behavior |
|--------------------|-----------------|-------------------|
| openai | OPENAI_API_KEY | Optional OPENAI_BASE_URL |
| anthropic | ANTHROPIC_API_KEY | Optional ANTHROPIC_BASE_URL |
| prime_intellect | PRIME_INTELLECT_API_KEY | Default pinference if PRIME_INTELLECT_BASE_URL and OPENAI_BASE_URL unset |

## Execution matrix

| Mode | Notes |
|------|--------|
| prime_intellect | Engine uses subprocess path; `LLM_*` + compat proxy wired in engine |
| openai / anthropic | Library path if `openhands.core` importable; else subprocess |

## Gate matrix (fixtures in CI)

| Flag | Negative test | Positive test |
|------|----------------|---------------|
| `--require-harness` | eval missing / run_id mismatch | healthy fake runpair + sidecars |
| `--require-compliance` | PF compliance file removed | default fake PF layout |
| `--require-patch-apply` | `n_applies_false > 0` | default |
| `--require-priced-models` | unknown model in summary | `gpt-4o` in fixture |
