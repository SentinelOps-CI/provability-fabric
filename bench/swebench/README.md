# SWE-bench bench runner

First-class PF workflow to run SWE-bench instances and emit `predictions.jsonl` plus PF evidence bundles.

## Overview

- **Single entry point**: `pf bench swebench run` (or run `bench/swebench/runner.py` directly).
- **Dataset ingestion**: `loader.py` loads instances via HuggingFace datasets (same as SWE-bench docs) and parses `instance_id`, `repo`, `base_commit`, and issue text (`problem_statement`, `hints_text`).
- **Workspace materialization**: `workspace.py` builds an isolated workspace per instance: clone repo at `base_commit`, write a task prompt file (issue + constraints), create a scratch dir for agent artifacts. Build is deterministic and idempotent for a given `instance_id`; a workspace manifest JSON is written and its SHA256 is recorded in the PF evidence log.
- **Modular components** (shared with `runner.py` for clarity and tests): `run_config.py` (`RunConfig`, `build_argument_parser`), `runner_core.py` (`run_swebench(config)` programmatic entry delegating to `_execute_run`), `workspace_manager.py` (wraps `materialize_workspace`), `instance_processor.py` (workspace + engine hook), `evidence_writer.py`, `predictions_writer.py`, `summary_writer.py`, `cost_reporter.py` (facade over `cost_report.py`), `engines/base.py` (`Engine` ABC), `engines/mock_engine.py` (`MockEngine`), `engines/openhands_adapter.py` (`OpenHandsEngine`, `get_engine`), `engines/deterministic_engine.py` (`DeterministicEngine`, interface completeness).
- **Outputs**:
  - `predictions.jsonl`: one line per instance in SWE-bench submission format (`instance_id`, `model_patch`, `model_name_or_path`). Exact SWE-bench schema so the harness runs without modification.
  - `predictions.pfmeta.jsonl`: PF metadata sidecar, one line per instance (same order and `instance_id` as predictions.jsonl). Fields: `instance_id`, `run_id`, `policy_hash`, `trace_hash`, `replay_bundle_hash`, `proof_artifact_hash` (if available), `empty_patch_reason` (if the patch was emitted empty; see below), `cost_metrics`. All hashes link back to evidence on disk.
  - **Predictions hash:** After writing predictions, the runner writes `predictions.sha256` in the same directory (SHA256 of the predictions file). The harness wrapper and compare use it to bind eval to the exact predictions file.
  - PF evidence: `runs/<run_id>/<instance_id>/` containing `run.log`, `model.patch`, `metadata.json` (with `engine_mode`, `engine_success`, `engine_error`), and when workspace is used `workspace_manifest.json` and `workspace_manifest_sha256` in metadata and run.log. When the engine runs, `engine_trace.json` is written with structured trace (prompts sent, tool calls, files modified). On OpenHands failure or empty trace with non-empty stderr, the runner also writes **`openhands_stderr_tail.txt`** (last 2000 chars of stderr) in the instance dir for debugging. **Patch apply check:** `patch_apply_check.json` records `git apply --check` result (applies, stderr, base_commit, resolved_commit, git_version) and when the patch is empty an **empty_patch_reason** (one of: `agent_no_changes`, `patch_too_large`, `diff_timeout`, `apply_check_failed`, `workspace_missing_or_failed`, `guard_denial_prevented_writes`). The same reason is written to `empty_patch_reason.txt` in the instance dir and to the pfmeta row. If the patch does not apply at base commit, the runner emits an empty patch for that instance so the harness counts it as failed. **Atomic predictions:** Predictions are written to `<out>.tmp`; only on successful completion are they renamed to the final path (atomic). **Run status:** In the same directory as the predictions file, the runner writes `run_status.json` with `run_id`, `status` (complete | partial | failed), `instances_planned`, `instances_written`, `first_error`, `created_at`. Use this to detect partial or failed runs; `validate_predictions` fails when status is not complete unless `--allow-partial` is set. **Env snapshot:** At run start the runner writes `runs/<run_id>/env.json` (python_version, platform, dataset, split, pip_freeze_hash, and when available openhands_version, datasets_version, swebench_version) and optionally `pip_freeze.txt` for reproducibility; `compare_runs` adds `env_drift` to the compare report when baseline and PF run envs differ and emits reproducibility fields from eval_metadata and env.json.
  - **PF-guarded runs:** `evidence/` is created unconditionally; `evidence/events.jsonl` is written with an initial `run_started` event so guard engagement is auditable even if the agent never issues commands. `policy_compliance_summary.json` is always written (compliant, violations, reason_codes, chain_tail_hash), including when there are zero tool calls or the engine crashes.
  - **Cost accounting**: `runs/<run_id>/<instance_id>/cost_report.json` per instance (prompt_tokens, completion_tokens, model_name, iterations, tool_calls, wall_clock_s, replay_s, proof_s, guarded). Aggregate: `runs/<run_id>/summary.json` and `runs/<run_id>/summary.csv` with one row per instance and columns run_id, instance_id, guarded, model_name, prompt_tokens, completion_tokens, iterations, tool_calls, wall_clock_s, replay_s, proof_s for easy comparison of baseline OpenHands vs PF-guarded OpenHands.
  - **Per-instance timing and termination:** `runs/<run_id>/<instance_id>/timing.json` (wall_clock_s, tool_calls, max_steps_reached, timeout_reached, termination_reason). **Operational definition of timeout:** timeout := runner set `timeout_reached` true (OpenHands subprocess raised `TimeoutExpired`) or `termination_reason == "max_steps"` (budget exhaustion). Kept separate from `guard_denial`, `empty_patch`, `apply_check_failed`, etc., so stress summaries can detect "PF makes hard repos worse" (timeout rate, wall-clock) over time.
  - Workspaces: `workspaces/<instance_id>/` with `repo/`, `task_prompt.md`, `scratch/`, and `workspace_manifest.json` (+ `workspace_manifest_sha256.txt`).

## Flow and why runs are long

1. **Load instances** (once): From dataset or file; filter by `--instance_ids` / `--max_instances`.
2. **Per instance**:
   - **Materialize workspace**: Clone repo at `base_commit` (or reuse existing workspace). When reusing, the runner now **resets the repo to `base_commit` and cleans the working tree** so every run starts from a clean state. Without that, a previous run’s leftover changes would be included in the next run’s diff and can produce huge or meaningless patches.
   - **Run the agent** (OpenHands): This is the **long part** (typically 2–7 minutes per instance). The agent edits files in `workspace/repo/`.
   - **Compute patch**: After the agent exits, the engine runs `git diff HEAD` (or path-restricted when the tree is huge). That diff can be very large or can **time out** on big repos (e.g. django, astropy), leading to empty or capped patches.
   - **Cap and apply check**: If the diff exceeds 2 MiB or `git apply --check` fails, the runner emits an empty patch for that instance.
3. **Output**: `predictions.jsonl` and evidence under `runs/<run_id>/<instance_id>/`.

So the costly step is the **agent run**; patch extraction and checks are short unless the working tree has a huge number of changes.

## Preflight

To avoid spending 10+ minutes on runs that are likely to fail or timeout:

1. **Run preflight first** (no agent, ~1–2 min for a few instances):
   ```bash
   pf bench swebench run --dataset Lite --split test --max_instances 5 --preflight
   ```
   This materializes workspaces, **ensures clean state** (reset on reuse), and prints a table: `instance_id`, commit count, current diff (0 = clean), and a short note (e.g. "large repo (full diff may timeout)"). Use it to see which instances have very large repos before you run the full agent.

2. **Use a small instance set for smoke tests**: e.g. `--max_instances 2` or `--instance_ids repo__repo-12345`. Reserve full runs for when you need harness results.

3. **Large repos**: If preflight shows "large repo" or diff timeout, set `PF_GIT_DIFF_TIMEOUT=300` (or higher) and expect path-restricted logic to reduce timeouts when the agent touches a bounded set of files.

4. **Clean workspaces**: Workspace reuse now resets to `base_commit` and runs `git clean -fd`, so you don’t need to delete `workspaces/` between runs to avoid dirty-state artifacts.

**Caveat:** Preflight does **not** guarantee full-run success. It only materializes workspaces and reports repo size hints; agent runs can still time out or produce empty patches on large repos (see Known limitations below).

## Known limitations (large repos and empty patches)

- **Large repos** (e.g. django, astropy, sympy) can still yield **empty patches** despite path-restricted diff and size caps. Causes: (1) full `git diff HEAD` or path-restricted diff times out (`PF_GIT_DIFF_TIMEOUT`); (2) diff exceeds `PF_MAX_PATCH_BYTES` (default 2 MiB); (3) trajectory has no `files_modified` so path-restricted fallback falls back to `--name-only`, which can also timeout on huge trees. The engine uses two-phase diff (stat then full or path-restricted) and a 50-path fallback when path-restricted is still over cap; that reduces but does not eliminate empty patches on very large or noisy working trees.
- **Preflight** only validates workspace materialization and clean state; it does **not** run the agent or patch extraction, so it cannot guarantee that a given instance will complete without an empty patch.
- **Mitigations:** Increase `PF_GIT_DIFF_TIMEOUT` (e.g. 300) for large repos; use preflight to identify "large repo" instances; inspect `patch_apply_check.json` and `empty_patch_reason` per instance; see "Troubleshooting: empty predictions" below.

**State of the art / improvements:** (1) Runner timeouts and patch caps are centralized in `bench/swebench/constants.py`; publish bundle shape and GOLDEN.ok keys are defined in `experiments/scripts/publish_bundle.py` and shared by the verifier and export. (2) Preflight and path-restricted diff reduce but do not eliminate empty patches on very large repos. (3) Reproducibility is supported via env.json, env_drift in compare, and `bench/swebench/requirements-swebench.txt` for version pinning.

## Entry points (pf CLI vs Python runner)

- **Recommended:** `pf bench swebench run` — single entry point; same behavior and options as the Python runner. Requires the PF CLI (`core/cli`) to be built and `pf` on PATH.
- **Alternative:** `python bench/swebench/runner.py` (from repo root) — direct Python entry point. Use when the `pf` CLI is not installed (e.g. in a venv without Go) or for debugging. Both entry points invoke the same `runner.py` logic and share `bench/swebench/constants.py` (e.g. `MAX_PATCH_BYTES`, `GIT_DIFF_TIMEOUT`). The experiment script `run-baseline-pf-cycle.sh` uses `pf` when available and falls back to `python bench/swebench/runner.py` otherwise.

Both `pf bench swebench run` and `python bench/swebench/runner.py` invoke the same runner logic; all timeouts and caps are defined in `bench/swebench/constants.py`.

## Prerequisites

- Python 3.8+
- For dataset-backed runs (no `--instances-file`): `pip install datasets`
- For workspace materialization: `git` on PATH and network access to clone GitHub repos
- **Docker:** SWE-bench eval and the harness expect the `docker` CLI and a running daemon (`docker info` succeeds). On a fresh Debian/Ubuntu VM (including GCP): `sudo apt-get update && sudo apt-get install -y docker.io`, then `sudo systemctl enable --now docker`. Use `sudo docker ...` or add your user to the `docker` group (`sudo usermod -aG docker "$USER"`, then re-login or `newgrp docker`). Smoke test: `docker run --rm hello-world`.
- For `--engine openhands`: OpenHands must be installed and importable (`pip install openhands` or use the official repo). The runner checks availability at start; if OpenHands is not available, the run exits with a clear error and does not create a run dir. Only `--engine mock` may produce toy outputs (for CI smoke tests).
- **API keys and LLM providers:** Set **OPENHANDS_PROVIDER** to `openai` (default), `anthropic`, or `prime_intellect`. For **openai**: **OPENAI_API_KEY**; for **anthropic**: **ANTHROPIC_API_KEY**; for **prime_intellect**: **PRIME_INTELLECT_API_KEY** (required). Optionally set **OPENHANDS_MODEL** (default `gpt-4o-mini`); the cycle and manifest can pin a different model. The engine sets **LLM_API_KEY**, **LLM_MODEL**, and when applicable **LLM_BASE_URL** for headless runs. For **prime_intellect**, **PRIME_INTELLECT_BASE_URL** (or **OPENAI_BASE_URL**) is optional; if unset, requests use Prime Inference **`https://api.pinference.ai/api/v1`** (so **`pit_*` keys are not sent to api.openai.com**). When any base URL is set, the engine may start a local **compatibility proxy** that normalizes request/response (e.g. assistant tool-call `content` and encoding) before forwarding upstream. Model IDs for Prime are normalized (e.g. `openai/gpt-4o`) so the upstream accepts them. **Task text truncation:** Set **PF_OPENHANDS_MAX_TASK_CHARS** (default **12000**) if you need to cap the task file size. SWE-bench problem statements are often much longer than 2k characters; an overly low cap truncates the instructions and hurts solve rate. If OpenHands fails inside tmux with "command too long", lower this value. See also experiments/exp-step2-lite-smoke/env-checklist.md.
- **Trajectory events but "no modified files":** If the log shows "trajectory: N events" and "git diff: skipped (no modified files ...); event kinds: ...", the agent ran (OpenHands subprocess finished in the repo cwd) but the working tree had no changes. The runner diffs the same repo directory OpenHands uses (`cwd=repo`). If event kinds are only **MessageEvent** (no **ActionEvent**), the model sent messages but did not run tools (edit_file, run_terminal_cmd, etc.) — the pipeline is correct; next steps are on the **OpenHands side** (version, headless behavior, model, or prompt). See **experiments/exp-step2-lite-smoke/openhands-headless-troubleshooting.md** for commands to confirm the diagnosis (e.g. `grep -o '"kind": "[^"]*"' workspaces/<id>/scratch/openhands_trajectory.jsonl | sort | uniq -c`), try a different model, run a minimal headless test, and compare with GUI.
- **Viewing trajectory and running OpenHands manually:** The trajectory is a **data file** (raw OpenHands CLI stdout), not a script. It contains banner lines (e.g. "Initializing agent...", "Agent is working") and JSON event blocks separated by `--JSON Event--`. View with `cat workspaces/<instance_id>/scratch/openhands_trajectory.jsonl` or `head -n 100 ...`; to count event kinds: `grep -o '"kind": "[^"]*"' workspaces/<instance_id>/scratch/openhands_trajectory.jsonl | sort | uniq -c`. Do not execute the file. To run the OpenHands CLI manually with headless, set **LLM_API_KEY** and **LLM_MODEL**: `export LLM_API_KEY="${OPENAI_API_KEY}" LLM_MODEL="${OPENHANDS_MODEL:-gpt-4o-mini}"` then e.g. `cd workspaces/astropy__astropy-12907/repo && openhands --headless --override-with-envs --json -t "Create an empty file named test_edit.txt."`
- Run from the repository root so that `bench/swebench/runner.py` is available and paths resolve correctly.

## Disk space (small GCP / CI VMs)

Default **10 GB** boot disks on cloud VMs are easy to exhaust when you run SWE-bench with Docker and HuggingFace-backed datasets. Space disappears into several buckets at once, so failures can look like flaky I/O, `docker pull` errors, broken `pip`/`uv` installs, or harness timeouts instead of a clear “disk full” message.

**What consumes space**

- **Docker**: harness and base images, build cache, and container layers under `/var/lib/docker`.
- **HuggingFace / `datasets`**: model and dataset cache, often multiple GiB after first use (default under `~/.cache/huggingface`).
- **Workspaces**: one git clone (or more) per instance under `workspaces/<instance_id>/`; large repos add up quickly.
- **Toolchains**: Python packages (wheels), `uv` managed Pythons, apt upgrades, logs, and run outputs under `runs/`.

**Checks**

- `df -h` (watch `/` and any extra volumes).
- `du -sh ~/.cache/huggingface workspaces runs /var/lib/docker 2>/dev/null` to see the largest consumers.

**Mitigations**

- **Resize** the boot disk in your cloud console (or start instances with **at least ~50 GB** if you plan repeated OpenHands + harness + dataset work).
- **Move caches**: set `HF_HOME` (and optionally Docker’s data root) to a larger attached data disk, not the tiny boot volume.
- **Prune** when safe: `docker system prune` / `docker image prune` (only if you do not need old images); delete stale `workspaces/` trees and old `runs/` you no longer need.
- **Do not** commit caches or `node_modules`-style trees into git; keep `.gitignore` aligned with local artifact dirs.

If jobs start failing mysteriously mid-run, check disk **before** chasing network or API issues.

## Direct-agent A/B gate (Prime Intellect)

`experiments/scripts/run_direct_agent_ab_gate.py` runs a **strict** comparison: baseline uses **`--engine openhands`** (the OpenHands agent against your configured LLM), candidate uses **`--engine direct_agent`**. The word **openhands** here is the **engine name**, not the LLM vendor. To drive both phases through **Prime Intellect** Inference, set:

```bash
export OPENHANDS_PROVIDER=prime_intellect
export PRIME_INTELLECT_API_KEY='pit_...'
export OPENHANDS_MODEL='google/gemini-2.5-flash'
# optional: export PRIME_INTELLECT_BASE_URL='https://...'
```

Then from the repo root (venv active, Docker up, `check_wsl_env.py` green):

```bash
python experiments/scripts/run_direct_agent_ab_gate.py \
  --model "${OPENHANDS_MODEL}" \
  --count 10 \
  --out-dir runs/direct-agent-ab-gate
```

Use `--count 1` and a fresh `--out-dir` for a short smoke. For **`pit_*`** keys, keep **`OPENAI_API_KEY`** unset unless you intentionally call OpenAI’s platform API; Prime defaults to **`https://api.pinference.ai/api/v1`** when no custom base URL is set (`bench/swebench/provider_env.py`). Run long jobs under **`tmux`** or **`screen`** on cloud VMs.

## Troubleshooting signatures (quick reference)

| Symptom | Likely cause | Recovery |
|--------|----------------|----------|
| OpenAI rejects **`pit_*`** API key | **`LLM_BASE_URL`** pointed at OpenAI or missing for Prime | Set **`OPENHANDS_PROVIDER=prime_intellect`** and **`PRIME_INTELLECT_API_KEY`**; leave bases unset to use default Prime Inference, or set **`PRIME_INTELLECT_BASE_URL`**. Check **`runs/<run_id>/env.json`**: **`llm_base_url_source`**, **`llm_base_url_effective`**. |
| Runner log says set **`OPENAI_API_KEY`** while using Prime | Stale preflight message | Fixed: preflight is provider-aware. If you patch locally, ensure **`bench/swebench/runner.py`** uses **`provider_env.openhands_preflight_log_line`**. |
| Harness **409** / container name in use | Stale **`sweb.eval.*.<run_id>`** after crash | Re-run **`run_swebench_eval.py`** with **`--rm-stale-eval-containers`**, or remove matching containers (see **experiments/exp-step2-lite-smoke/troubleshooting-compare-results.md**). |
| **`compare_runs --require-harness`** fails on **`run_id` mismatch** | **`eval_metadata.json`** or **`run_status.json`** from an older harness | Re-run harness for the current predictions or align **`run_id`** fields. |
| **`--require-priced-models`** fails | Model string in **`cost_report.json`** not in **`model_pricing.py`** | Add pricing or use a known **`OPENHANDS_MODEL`** id. |

Shared provider resolution (keys, base URL fallbacks, model normalization for Prime) lives in **`bench/swebench/provider_env.py`** and is used by the OpenHands engine, **`ensure_openhands_config.py`**, and the runner **`env.json`** fields above. For **`prime_intellect`**, the engine uses the **subprocess** OpenHands path so the local compatibility proxy and **`LLM_*`** env wiring always apply.

For a consolidated pytest command list, budget drift table, Prime smoke steps, and compare gate checklist, see **`docs/internal/swebench-stabilization-regression-matrix.md`**.

## Running locally

### Via PF CLI (recommended)

From the repository root:

```bash
# Run one instance (use --instance_ids to target a single instance)
pf bench swebench run --dataset Lite --split test --instance_ids django__django-12345 --out predictions.jsonl --engine openhands

# Run up to N instances
pf bench swebench run --dataset Lite --split test --max_instances 3 --out predictions.jsonl --engine openhands

# Full options
pf bench swebench run \
  --dataset Lite \
  --split test \
  --instance_ids id1,id2 \
  --max_instances 10 \
  --out predictions.jsonl \
  --engine openhands \
  --runs-dir runs
```

### Direct Python

From the repository root:

```bash
python bench/swebench/runner.py \
  --dataset Lite \
  --split test \
  --instance_ids django__django-12345 \
  --out predictions.jsonl \
  --engine openhands
```

### Using a local instances file

If you do not want to use HuggingFace datasets, provide a JSON or JSONL file with instance records (each with at least `instance_id`; other fields follow SWE-bench-style keys). Use `--no-workspace` to skip clone/checkout when instances lack a real repo or you only need predictions:

```bash
pf bench swebench run --instances-file my_instances.jsonl --max_instances 1 --out predictions.jsonl --no-workspace
```

### With workspace materialization

By default the runner materializes a workspace per instance (clone at `base_commit`, task prompt, scratch dir). The workspace manifest is hashed and recorded in the evidence log:

```bash
pf bench swebench run --dataset Lite --split test --max_instances 1 --out predictions.jsonl --workspaces-dir workspaces
```

## Options

| Option | Description |
|--------|-------------|
| `--dataset` | `Lite`, `Verified`, or `Full` (SWE-bench dataset variant). |
| `--split` | Dataset split, e.g. `test` or `dev`. |
| `--instance_ids` | Comma-separated instance IDs; only these are run. |
| `--max_instances` | Cap on number of instances to run. |
| `--instances-file` | Load instances from a local JSON/JSONL file instead of HuggingFace. |
| `--instance-ids-file` | Path to file with one instance_id per line; filter dataset to these IDs. |
| `--experiment-dir` | Experiment directory containing `manifest.json`; runner uses `budgets.max_steps` and `budgets.timeout_sec` as defaults for `--openhands-max-iterations` and `--openhands-timeout` when those flags are not set. |
| `--out` | Path for `predictions.jsonl`. |
| `--skip-existing` | Resume: skip instances already present in `--out`; copy their lines and pfmeta from existing files so the run can continue from the next instance. |
| `--engine` | Engine: `openhands` (default) or `mock`. `mock`: no OpenHands dependency; for CI smoke tests (deterministic trace, one denied command when guarded). |
| `--runs-dir` | Base directory for evidence (`runs/<run_id>/<instance_id>/`). |
| `--run-id` | Optional explicit run ID; otherwise auto-generated. |
| `--workspaces-dir` | Base directory for materialized workspaces (default `workspaces`). |
| `--no-workspace` | Skip workspace materialization (no clone/checkout). |
| `--openhands-model` | OpenHands model name (default `gpt-4o-mini`). |
| `--openhands-max-iterations` | OpenHands max iterations (default 25). When `--experiment-dir` is set, default comes from manifest `budgets.max_steps`. |
| `--openhands-timeout` | OpenHands timeout in seconds (default **1200** in `RunConfig`; use manifest `budgets.timeout_sec` when `--experiment-dir` is set and the flag was not passed). |
| `--guarded` | Run OpenHands through PF-Guarded Runtime (tool gateway, ledger, compliance). |
| `--policy` | Policy pack name (e.g. `swebench_safe_v1`). Policy hash is included in evidence and PF metadata sidecar. |
| `--prove` | Run proof step: build policy-trace Lean proof; write `proof.ok` and `proof_artifact_hash.txt` on success, `proof_failure.json` on failure. |
| `--proofs-dir` | Path to Lean proofs dir (default: repo `spec-templates/v1/proofs`). Used when `--prove` is set. |
| `--dataset-cache-dir` | HuggingFace dataset cache directory (must be writable; e.g. `./hf_cache` or leave unset for default). |

### Logging and performance

Progress and timing are logged to stderr with prefixes `[pf-swebench]` and `[openhands-engine]`: instance index, workspace time, engine start/done and patch length, and (when verbose) library vs subprocess path, subprocess returncode, git diff time, trajectory event count. Set `PF_SWEBENCH_QUIET=1` to suppress these logs.

- **Faster runs**: (1) Workspace build is idempotent; an existing workspace with matching `base_commit` is reused (no re-clone). (2) When the agent made no file edits, the engine skips the full git diff after a short name-only check (5s by default; set `PF_NO_EDIT_FAST_CHECK_TIMEOUT` to tune), saving ~7–10s per no-edit instance. (3) Use `--dataset-cache-dir` to point the HuggingFace cache to a fast disk. (4) Use `--max_instances` for smoke runs. (5) Use `--skip-existing` to resume an interrupted run (same `--out` and `--runs-dir`); instances already in the predictions file are skipped. (6) For parallel throughput, run multiple runner processes with different instance subsets (e.g. split `instance_ids.txt` in two, run two jobs in parallel, then run harness/compare on the combined run dirs or merge predictions if your workflow allows).
- **Where time goes**: Load instances (once); per instance: workspace materialization (or reuse), then engine (OpenHands), which dominates; then git diff (or fast-path skip) and evidence write. Default per-instance timeout is **1200s** unless overridden by manifest (`budgets.timeout_sec` with `--experiment-dir`) or `--openhands-timeout`.

### Mock engine (CI smoke)

Use `--engine mock` to run the pipeline without OpenHands: deterministic, fast, no model calls. Writes 2–3 tool calls into the trace; when guarded, runs one denied command (e.g. `curl example.com`) so the guard writes exactly one violation event (`reason_code=binary_forbidden`). Use for CI to assert JSONL schema, evidence layout, and guarded-mode invariants.

- **Baseline** (`--engine mock`, no `--mode pf_guarded`): no violation events.
- **Guarded** (`--engine mock --mode pf_guarded`): exactly one violation event with `reason_code=binary_forbidden`.

Smoke tests: from repo root run `pytest tests/test_swebench_runner_smoke.py -q` (full runner + mock/guarded; CI uses this). Lighter mock-only check: `python bench/swebench/test_mock_engine_smoke.py`.

### Replay

To replay a run (reconstitute patch from captured tool I/O and verify hash), from repository root:

```bash
pf bench swebench replay --run_id <run_id> [--instance_id <id>] [--runs-dir runs] [--json]
```

Requires the workspace to still exist at the path in `workspace_manifest.json` for each instance. See `replay/README.md`. **Replay sample (experiments):** After a PF run and harness, `experiments/scripts/run_replay_sample.py` selects N instances that are harness-resolved with zero violations, runs replay, and writes `replay_summary.json`; the experiment compare script merges it into compare.json (replay.sample_size, success_rate, mismatch_count, replay_fail_reasons_topN).

## Dataset ingestion and workspace

- **loader.py**: Load dataset via HuggingFace `datasets` (same IDs as SWE-bench docs: `princeton-nlp/SWE-bench_Lite`, etc.). Parses `instance_id`, `repo`, `base_commit`, `problem_statement`, `hints_text`, and other standard fields into a `SWEbenchInstance` dataclass. Also supports loading from a local JSON/JSONL file.
- **workspace.py**: For each instance, materializes an isolated workspace under `workspaces_dir/<sanitized_instance_id>/`: clones the repo (HTTPS GitHub URL from `repo`), checks out `base_commit`, writes `task_prompt.md` (issue text plus constraints/hints), and creates `scratch/` for agent artifacts. Writes `workspace_manifest.json` (instance_id, repo, base_commit, paths, resolved_commit) and `workspace_manifest_sha256.txt`. The manifest is canonicalized and SHA256-hashed; the hash is written into the PF evidence log (run.log and metadata.json) and a copy of the manifest is stored in the evidence dir. Workspace build is deterministic and idempotent for a given `instance_id` and `base_commit`.

## Acceptance criteria

- Running on one instance produces:
  - `predictions.jsonl` with exactly one line in SWE-bench format.
  - A PF evidence folder `runs/<run_id>/<instance_id>/` with `run.log`, `model.patch`, `metadata.json` (including `engine_mode`, `engine_success`, `engine_error`), and `patch_apply_check.json`; when workspace is used, also `workspace_manifest.json` and `workspace_manifest_sha256` in metadata and run.log.
- For PF-guarded runs, each instance has `evidence/events.jsonl` (with at least a `run_started` event) and `policy_compliance_summary.json`.
- For a given `instance_id`, workspace build is deterministic and idempotent; workspace manifest JSON is written and hashed into the PF evidence log.
- Filters: `--instance_ids` and/or `--max_instances` are supported.
- With `--engine openhands`, if OpenHands is not available the run exits non-zero and does not create a valid run dir; no stub patch is emitted.

## Schemas

Optional PF run metadata schema:

- `schemas/pf_run_metadata.json`: JSON Schema for `metadata.json` in each instance evidence directory.

Experiment report schemas (under `experiments/schemas/`):

- `compare_report.schema.json`: Required shape of compare.json (baseline, pf, delta, patch_apply, violation_reasons_top10, optional env_drift, empty_patch_reasons_topN, reproducibility fields: dataset_name, split, datasets_version, swebench_version, harness_dataset_id, openhands_version; optional replay section: sample_size, success_rate, mismatch_count, replay_fail_reasons_topN; optional policy section: reason_codes_topN, denied_commands_topN, commands_seen_topN; optional budget_drift). `compare_runs.py` optionally validates the written report with jsonschema when the library is installed.
- `harness_report_min.schema.json`: Minimum harness run report (resolved_ids or resolved_instances, total_instances).

## PF-Guarded Runtime (--guarded / --mode pf_guarded)

When `--guarded` is set or `--mode pf_guarded` is used, OpenHands runs through a **tool gateway** that mediates shell exec: every command is checked against policy before execution. Forbidden actions (e.g. network binaries like curl, or writes outside workspace) **fail closed** and are recorded as violations.

- **Evidence is mandatory:** For each instance, the runner creates `evidence/` and writes an initial **run_started** event to `evidence/events.jsonl` before the agent runs, so guard engagement is auditable even if the agent crashes or issues no commands. **policy_compliance_summary.json** is always written (compliant, violations, reason_codes, chain_tail_hash), including when there are zero tool calls or the engine fails.
- **events.jsonl**: Hash-chained append-only stream. Optional: set `PF_LEDGER_URL` to POST events to a PF ledger API. See `guard/README.md`.
- **Mode `pf_guarded`**: Enables guarded run with policy; use `--policy swebench_safe_v1` (or omit for default). Equivalent to `--guarded` plus policy load. Policy hash is recorded in each instance bundle (`metadata.json` and `run.log`).
- **Every denied action** produces a **structured violation event** in `evidence/events.jsonl` (event_type `violation`, payload includes `violation`, `reason_code`) and is reflected in the **final compliance summary** (`policy_compliance_summary.json`: pass/fail, violations count, reason_codes list).
- **Recoverable denials**: By default, policy denials are recoverable: the guard returns exit code 125 for the denied command only; the agent (OpenHands) can continue. Fail-fast (abort run on first denial) is not enabled unless explicitly configured (e.g. future `PF_GUARD_FAIL_FAST=1`).

**Validation**: After a guarded run, run `python bench/swebench/validate_pf_run.py runs/<run_id>` to check policy hash in each instance bundle, presence of compliance summary with pass/fail and reason_codes, and consistency of violation events. **Policy regression tests:** `tests/test_policy_guard_deny_allow.py` locks deny/allow behavior: deny curl, wget, git clone https, pip install git+https; allow python -m pytest, pip install -e ., make test, grep, sed; allow writes only under workspace; deny writes to /tmp or -o to forbidden paths. The guard denies git/pip when the command contains https:// or git+https.

**SWE-bench harness evaluation**: Use the same harness for baseline and PF predictions; see `experiments/README.md` and `experiments/scripts/run_swebench_eval.py`, `collect_eval_results.py` for commands and pass/fail plus failure-bucket collection. The harness wrapper writes **eval_metadata.json** in each eval dir with run_id (from run_status.json next to the predictions file), predictions_sha256 (if present), dataset_name, split, and datasets/swebench versions so compare can enforce run/eval binding. The experiment compare script (`experiments/scripts/compare_runs.py`) aggregates `patch_apply_check.json` (including empty_patch_reason) and emits **empty_patch_reasons_topN** in compare.json; it supports `--require-harness` (which asserts run_id consistency and optional predictions hash), `--require-compliance`, and `--require-patch-apply`; see experiments/README.md.

## Platform: real run + harness on WSL/Linux only

The entire **real run + harness** loop (agent runs and SWE-bench harness evaluation) must run on **WSL or Linux**, not Windows-native:

- **OpenHands** uses **fcntl** (Unix-only).
- The **SWE-bench harness** uses **resource** (Unix-only).
- **Docker** is required by the harness.

On native Windows the runner allows only `--engine mock` or `--mode deterministic`; any other run exits with an error. Use WSL (Ubuntu recommended) or Linux for baseline, PF-guarded, and harness evaluation.

**Minimal environment checklist (WSL):** Before runs, verify `resource`, `fcntl`, `docker info`, `datasets`+`swebench`, and `openhands`. See **experiments/exp-step2-lite-smoke/env-checklist.md** and run `python experiments/scripts/check_wsl_env.py` from the repository root. If any check fails, do not proceed to runs.

## OpenHands engine adapter

- **engines/openhands_engine.py**: PF invokes OpenHands as a library when `openhands.core` is importable, or via **CLI subprocess** otherwise. For **`OPENHANDS_PROVIDER=prime_intellect`**, the engine **always** uses the subprocess path so **`LLM_*`**, the optional Prime strict-compat proxy, and normalized **`OPENHANDS_PROVIDER`** are passed to the OpenHands CLI consistently. The CLI path uses `openhands --headless --override-with-envs --json --file <task>` (task file avoids argv limits). `solve(workspace_path, task_text, config)` returns `SolveResult(patch_diff_str, trace, success, error)`. Config: `model_name`, `max_iterations`, `temperature=0`, `timeout_seconds`. The engine runs in the workspace `repo/` directory, then computes the patch via `git diff HEAD`. Structured trace: `prompts_sent`, `tool_calls`, `files_modified` (and optional `raw_events`); written to `engine_trace.json` in the instance evidence dir.

**Patch size cap and git diff:** All timeouts and thresholds are defined in **`bench/swebench/constants.py`** (single source of truth; engine imports from there).

- **MAX_PATCH_BYTES** (default 2 MiB, override with `PF_MAX_PATCH_BYTES`): If the raw diff exceeds this, the runner emits an empty patch and writes **`runs/<run_id>/<instance_id>/diff_stat_when_too_large.txt`** with `git diff HEAD --stat` (truncated) for debugging. **patch_apply_check.json** includes `patch_capped_reason: "size"` and `diff_stat_file: "diff_stat_when_too_large.txt"` when applicable.
- **GIT_DIFF_TIMEOUT** (default 120s, override with `PF_GIT_DIFF_TIMEOUT`): If full `git diff HEAD` does not complete in time, the engine may return a short fallback string; the apply check then fails and the runner emits an empty patch and sets `patch_capped_reason: "timeout"` in **patch_apply_check.json**.
- **Two-phase diff:** The engine runs `git diff HEAD --stat` first (`PF_DIFF_STAT_TIMEOUT`, default 20s). If more than `PF_DIFF_STAT_FILE_THRESHOLD` (default 200) files changed, it skips the full diff and uses a **path-restricted** diff (`git diff HEAD -- <paths>`) from the trace’s `files_modified` (or from `--name-only` with `PF_NAME_ONLY_QUICK_TIMEOUT`, default 30s), avoiding long timeouts on huge working-tree changes.
- **Path-restricted fallback:** If the full diff is over the size cap or times out, the engine retries with a path-restricted diff (timeout `PF_PATH_DIFF_TIMEOUT`, default 60s). When path-restricted is still over cap, it tries at most `PF_PATH_RESTRICTED_MAX_PATHS` (default 50) paths. When that yields a valid patch under the cap, that patch is used so you get a minimal, auditable patch instead of empty.
- **Runner invariants for openhands:** At start of run the runner checks that OpenHands is available (library or CLI); if not, it exits with a clear error and does not create a run dir. For each instance, the runner requires a non-empty patch and a trace with content (at least one of: non-empty `tool_calls`, non-empty `files_modified`, or `raw_events` length > 0). If the trace is empty or the patch is empty, the instance is treated as an engine failure (empty patch emitted). **metadata.json** per instance includes `engine_mode` (`openhands` | `mock` | `deterministic`), `engine_success`, and `engine_error` so you can compute solve rate conditional on the engine actually having run.
- OpenHands expects runtime attachment and controller execution (see OpenHands evaluation harness docs); this adapter uses the process runtime so the agent operates directly in the materialized repo directory.

## Troubleshooting: empty predictions or "model_patch is empty or not a diff"

1. **Check patch_apply_check.json** in `runs/<run_id>/<instance_id>/`. If `applies` is false, read `stderr`. If present, **patch_capped_reason** indicates why the patch was not used: `"size"` (diff exceeded MAX_PATCH_BYTES), or `"timeout"` (git diff did not complete in time).
2. **When patch_capped_reason is "size"**: Open **diff_stat_file** (usually `diff_stat_when_too_large.txt`) in the same directory to see which files changed. If the list is mostly build/cache or unrelated paths, consider excluding those from the workspace or increasing `PF_MAX_PATCH_BYTES` only if you accept very large patches.
3. **When patch_capped_reason is "timeout"**: The repo had too many or too large changes for `git diff HEAD` to finish within `PF_GIT_DIFF_TIMEOUT`. Increase `PF_GIT_DIFF_TIMEOUT` (e.g. 300) for large repos, or run on instances with smaller repos. The engine’s two-phase and path-restricted logic should already avoid full-diff timeouts when the agent touched a bounded set of files.
4. **Validation message "model_patch is empty or not a diff"**: Emitted when the runner intentionally wrote an empty patch (cap or apply check failed). Use the steps above to confirm the cause from evidence.

### Run investigation: trajectory 0 events, 9999 files, path-restricted over cap, django timeout

Typical run logs and what they mean:

- **trajectory: 0 events**: The engine reads the agent trajectory from `scratch/openhands_trajectory.json` or `openhands_trajectory.jsonl`. When using the OpenHands **CLI subprocess** (no library), the CLI did not previously write to that path. The engine now runs the CLI with **`--json`** and captures stdout to **`scratch/openhands_trajectory.jsonl`** (JSONL format). The parser supports both a single JSON file and JSONL (one JSON object per line). So after this change, trajectory events and **files_modified** from the agent (e.g. write/edit_file actions) can be used for path-restricted diff.
- **git diff: skipped full (9999 files)**: **9999** is the fallback from **`_get_diff_stat_file_count`** when `git diff HEAD --stat` times out (DIFF_STAT_TIMEOUT, default 20s) or parsing fails. So the engine correctly skipped the full diff and used path-restricted. If trajectory had 0 events, **paths** came from **`git diff HEAD --name-only`** with **NAME_ONLY_QUICK_TIMEOUT** (default 30s) so a partial list is available quickly for path-restricted fallback (e.g. django).
- **path-restricted 28.50s patch_len=5680802**: Path-restricted diff with the first DIFF_STAT_FILE_THRESHOLD (200) paths still produced a 5.4MB patch (over 2MB cap). The engine tries again with at most **PATH_RESTRICTED_MAX_PATHS_FALLBACK** (50) paths. If that patch is under the cap, it is used so you get a smaller, often source-heavy subset instead of empty.
- **git diff: 140.15s patch_len=81** (django): Full diff was run (file count was ≤200), hit GIT_DIFF_TIMEOUT (120s), and returned the short fallback string (81 bytes). With NAME_ONLY_QUICK_TIMEOUT (30s) for `--name-only`, the engine gets a partial path list quickly; then when full diff times out, it tries **path-restricted** with that list so django can still yield a valid patch when the agent touched a bounded set of files.

## Reproducibility (dataset and OpenHands version drift)

Dataset, harness, and OpenHands versions affect solve rates and behavior. Mitigations in place:

- **Recorded per run:** At run start the runner writes **`runs/<run_id>/env.json`** with `python_version`, `platform`, `dataset`, `split`, and when available `openhands_version`, `datasets_version`, `swebench_version`, and `pip_freeze_hash`. The compare script (**compare_runs.py**) emits **env_drift** in compare.json when baseline and PF run envs differ (e.g. different pip_freeze_hash or version fields), and fills **reproducibility** fields from eval_metadata and env (dataset_name, split, datasets_version, swebench_version, harness_dataset_id, openhands_version).
- **Recommendation for golden and release runs:** Pin versions so baseline and PF runs (and any re-runs) use the same environment. For example: `pip install datasets==X.Y.Z swebench==A.B.C openhands==...` (or use a locked requirements file). Record the versions in the experiment manifest or in a run README; check **env_drift** after compare and fix the environment if it is non-empty before treating a run as golden. For CI and scheduled stress runs, pin in the workflow or use a container image with fixed versions.
- **Pinned requirements:** See `bench/swebench/requirements-swebench.txt` for recommended packages (datasets, swebench, openhands). For golden runs, install from a pinned copy of this file and record the pip hash in the run README; check **env_drift** in compare.json after each run.
- **Recording the pip hash in the run README:** The runner writes **`pip_freeze_hash`** (SHA256 of `pip freeze` output) in `runs/<run_id>/env.json` at run start. For strict reproducibility, add a line to the experiment run README or run-ids.md, e.g. `pip_freeze_hash: <value>` (copy from env.json), so golden runs are auditable and env_drift in compare.json can be checked against it.

Reproducibility remains a concern when datasets or OpenHands are updated between runs; env.json and env_drift surface differences so you can attribute solve-rate changes to environment vs. code changes.

## Integration notes

- Evidence layout is designed to align with PF evidence bundles and audit needs.
- For the full experiment cycle (baseline + PF + harness + compare + publish), see [experiments/README.md](../../experiments/README.md) and [experiments/exp-step2-lite-smoke/commands.md](../../experiments/exp-step2-lite-smoke/commands.md).
