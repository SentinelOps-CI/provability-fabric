# Environment checklist (WSL/Linux required)

The **real run + harness** loop (Step 2: agent runs and SWE-bench harness evaluation) cannot be completed on Windows-native because:

- OpenHands uses **fcntl** (Unix-only).
- The SWE-bench harness uses **resource** (Unix-only).
- Docker is required by the harness and is used from the evaluation environment.

**Run baseline, PF-guarded, and harness evaluation inside WSL (Ubuntu recommended) or on Linux.**

## Debian/Ubuntu cloud VM (GCP and similar)

1. **Repository path:** Docs may show a placeholder like `/path/to/provability-fabric`. Use your real clone, e.g. `cd ~/provability-fabric`, and run every script from that directory.
2. **`python: command not found`:** Minimal Debian images often install only **`python3`**. After **`setup_swebench_venv.sh`**, **`python3 experiments/scripts/check_wsl_env.py`** re-executes into **`.venv-wsl/bin/python`** when that venv exists (system **`python3`** has no **`datasets`**/**`openhands`**). Alternatively: **`./.venv-wsl/bin/python experiments/scripts/check_wsl_env.py`** or **`source .venv-wsl/bin/activate`** then **`python ...`**.
3. **`smoke_direct_agent_one.sh: No such file or directory`:** The clone on the VM is older than the commit that added the script. Run **`git fetch`** and **`git pull`** on the branch you use for Step-2 (or merge from **`main`**), then check **`test -f experiments/scripts/smoke_direct_agent_one.sh`**.
4. **Disk almost full (`df -h /` shows ~98% or &lt;1 GiB free):** Long runs and Docker layers will fail unpredictably. Before smoke or the full cycle: **`docker system prune -af`** (removes unused images), remove stale **`runs/`** and **`workspaces/`** trees you no longer need, and consider **`HF_HOME`** on a larger disk or **resize the GCP boot/data disk** (10 GiB boot disks are usually too small for this workflow).

## Credentials (one-time in WSL)

**Provider:** Set **`OPENHANDS_PROVIDER`** to `openai` (default), `anthropic`, or `prime_intellect`. The cycle script validates the matching key before baseline/PF runs.

| Provider | Required env |
|----------|----------------|
| `openai` | `OPENAI_API_KEY` |
| `anthropic` | `ANTHROPIC_API_KEY` (optional `ANTHROPIC_BASE_URL`) |
| `prime_intellect` | `PRIME_INTELLECT_API_KEY` (required). **`PRIME_INTELLECT_BASE_URL` or `OPENAI_BASE_URL`** optional; if both are unset, the runner uses Prime Inference **`https://api.pinference.ai/api/v1`** (OpenAI-compatible). Set a custom base only for non-default endpoints. |

- **Option A:** Repo-root `.env` (sourced by **`run-baseline-pf-cycle.sh`**) with the keys above. For Prime Intellect, add `PRIME_INTELLECT_API_KEY` and base URL.
- **Option B:** Export in the shell before the cycle.

**Hugging Face Hub (dataset load / rate limits):** The SWE-bench harness and `datasets` load **`SWE-bench/SWE-bench_Lite`** from the Hub. Without a token you may see warnings about unauthenticated requests. Set **`HF_TOKEN`** (or run `huggingface-cli login`) in WSL if downloads are slow, rate-limited, or fail on gated assets. This is optional for the public Lite dataset but recommended for stable CI and large runs.

**Model:** **`OPENHANDS_MODEL`** overrides **`manifest.json`** `model.id`. After Phase 1.2 the cycle resolves one effective model and passes **`--openhands-model`** to every run (hard-enforced).

**OpenHands headless:** The PF engine runs OpenHands with **`--override-with-envs`** and sets **LLM_API_KEY**, **LLM_MODEL**, and **LLM_BASE_URL** (when applicable) from the provider above. No GUI or "run openhands once" is required. For **manual** headless CLI runs you must set the same env vars in your shell: `export LLM_API_KEY="${OPENAI_API_KEY}" LLM_MODEL="${OPENHANDS_MODEL:-gpt-4o-mini}"` (after sourcing `.env` or setting OPENAI_API_KEY); otherwise OpenHands exits with "Missing required environment variable(s): LLM_API_KEY, LLM_MODEL". To **view** trajectory output (do not execute the file), use `cat workspaces/<instance_id>/scratch/openhands_trajectory.jsonl` or `head -n 20 ...`. If runs produce only **MessageEvent** (no **ActionEvent**) and empty patches, next steps are on the OpenHands side: see **openhands-headless-troubleshooting.md** in this directory for version check, minimal headless test, model override, and GUI comparison. The cycle script runs **`experiments/scripts/ensure_openhands_config.py`** as a fallback to create `~/.openhands/config.toml` when missing.

Full Step-2 cycle (baseline run, PF run, validations, harness, gated compare, delta triage): **`bash experiments/scripts/run-baseline-pf-cycle.sh`** or **`bash experiments/scripts/wsl-baseline-pf-cycle.sh`** from repo root in WSL. Pass an optional instance count to limit runs (e.g. **`bash experiments/scripts/wsl-baseline-pf-cycle.sh 2`** for a 2-instance test). Both helpers align baseline/PF **`validate_predictions`** with **`--allow-empty-patch`** where the canonical cycle allows empty patches.

**Agent tuning (fewer empty patches / timeouts):** OpenHands budgets come from **`experiments/exp-step2-lite-smoke/manifest.json`** (`max_steps`, `timeout_sec`) when you pass **`--experiment-dir`** to the runner without overriding flags. The cycle exports **`OPENHANDS_TIMEOUT`** (default 1200s; increase for slow models). Override iterations with **`--openhands-max-iterations`** on the runner if needed. Keep baseline and PF budgets symmetric so **`compare_runs`** budget drift checks pass. Task-size limits for the subprocess engine are described in engine logs (e.g. **`PF_OPENHANDS_MAX_TASK_CHARS`**); see **openhands-headless-troubleshooting.md** if truncation correlates with failures.

## Building pf and putting it on PATH (WSL)

The full parity cycle script `run-baseline-pf-cycle.sh` invokes `pf bench swebench run`. To have `pf` available in WSL:

1. From WSL, go to the repo (e.g. `cd /mnt/c/Users/<user>/provability-fabric` or your clone path).
2. Build and install: `go build -o ~/.local/bin/pf ./core/cli/pf`
3. Ensure `~/.local/bin` is on PATH: `echo 'export PATH="$HOME/.local/bin:$PATH"' >> ~/.bashrc && source ~/.bashrc`
4. Verify: `which pf` and `pf bench swebench run --help`

If `pf` is not on PATH, `run-baseline-pf-cycle.sh` falls back to calling `python bench/swebench/runner.py` from the repository root with the same arguments (Run ID is still parsed from stdout).

## Minimal environment checklist (WSL)

Inside Windows Subsystem for Linux, verify the following **before** proceeding to runs. If any check fails, do not proceed.

```bash
# On bare Debian/GCP without a `python` symlink, use python3 here, or: source .venv-wsl/bin/activate
python3 -c "import resource; print('resource ok')"
python3 -c "import fcntl; print('fcntl ok')"
docker info
python3 -c "import datasets, swebench; print('datasets+swebench ok')"
python3 -c "import openhands; print('openhands ok')"
```

**Reproducibility (version pinning):** For golden or comparable runs, pin `datasets`, `swebench`, and `openhands` to the same versions for baseline and PF (e.g. `pip install -r bench/swebench/requirements-swebench.txt` with pinned versions, or `pip install datasets==X.Y.Z swebench==A.B.C`). The runner records versions in `runs/<run_id>/env.json`; compare reports **env_drift** when they differ. See bench/swebench/README.md "Reproducibility" and `bench/swebench/requirements-swebench.txt`.

**LLM routing audit (Prime vs OpenAI):** OpenHands runs also record **`openhands_provider`**, **`llm_base_url_source`**, **`llm_base_url_effective`**, and **`prime_team_id_set`** in **`env.json`** (no secrets). Logic is centralized in **`bench/swebench/provider_env.py`**. For a full pytest list and WSL smoke checklist, see **`docs/internal/swebench-stabilization-regression-matrix.md`**.

## GCP / overnight runs (Prime + `direct_agent`)

Before a long **`run-baseline-pf-cycle.sh`** or **`run_gcp_vm_swebench_baseline_pf_compare.sh`**:

1. **`git rev-parse HEAD`** — include fixes for Prime + `direct_agent` (vendor model ids on raw HTTP, proxy upstream timeout, HTTP retries). The cycle exports **`PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S`** to match **`OPENHANDS_TIMEOUT`** (default 1200s); do not leave an old **`180`** override unless you intend short timeouts.
2. **Disk** — keep **≥1–2 GiB** free on `/` (`df -h`); prune Docker and journals if needed.
3. **Quick smoke** — **`bash experiments/scripts/smoke_direct_agent_one.sh`** (one Lite instance, `direct_agent`). Expect **`patch_len > 0`** in the script output; if zero, fix API/model/env before a 20×2 run.
4. **After a run** — **`compare.json`** includes **`meta.generated_at`** and **`meta.*_run_dir`** when produced by **`compare_runs.py`**. Re-run compare with explicit **`--baseline-run-dir`** / **`--pf-run-dir`** for the run pair you mean to grade; do not rely on an old **`compare.json`** mtime. Inspect artifacts with **`python3 experiments/scripts/run_health_snapshot.py`** (or **`./.venv-wsl/bin/python`** / activated venv) **`--run-dir runs/.../<run_id>`**.

**Optional env (Prime / robustness):** **`PF_DIRECT_AGENT_HTTP_RETRIES`** (default 3), **`HF_TOKEN`** (Hub rate limits). **`PF_DIRECT_AGENT_FALLBACK_OPENHANDS`** defaults to **`1`** in **`run-baseline-pf-cycle.sh`** (OpenHands subprocess after eligible `direct_agent` failures; matches smoke). Set **`PF_DIRECT_AGENT_FALLBACK_OPENHANDS=0`** or **`PF_CYCLE_STRICT_DIRECT_AGENT=1`** for strict direct_agent-only runs (higher risk of empty patches with frontier models).

Or run the preflight script from the repository root (exits non-zero if any check fails):

```bash
python3 experiments/scripts/check_wsl_env.py
# Or: source .venv-wsl/bin/activate && python experiments/scripts/check_wsl_env.py
```

## Dedicated venv (avoid OpenHands conflicts)

OpenHands pulls in many dependencies (litellm, opentelemetry, fastmcp, etc.). Installing it in the **same** Python environment as other projects (e.g. corridor-os, crewai, guardrails-ai, instructor, streamlit) often causes version conflicts. Use a **dedicated venv** for SWE-bench and OpenHands only.

**Recommended (WSL, one command):** From repo root in WSL:

```bash
bash experiments/scripts/setup_swebench_venv.sh
```

This creates or reuses `.venv-wsl`, installs `datasets`, `swebench`, and `openhands` from `bench/swebench/requirements-swebench.txt`, and runs the preflight check. The cycle script `run-baseline-pf-cycle.sh` automatically uses `.venv-wsl` if present.

**Manual:** Create a fresh venv, activate it, then install only the SWE-bench deps:

```bash
python3 -m venv .venv-wsl
. .venv-wsl/bin/activate
pip install -r bench/swebench/requirements-swebench.txt
python experiments/scripts/check_wsl_env.py
```

Do **not** install OpenHands with `pip install openhands` into a global Python or an env that already has corridor-os, crewai, guardrails-ai, or other packages with strict version pins; use the project venv and the requirements file above.

## Network-unavailable (negative capability)

To demonstrate that the guard denies network tooling, you can optionally verify in the same WSL environment:

- Run a PF-guarded run (or use an existing run); in policy compliance or events, confirm that commands such as `curl`, `wget`, or `pip install <url>` are denied (reason codes e.g. `network_denied` or `binary_forbidden`).
- Optionally, disable network at the OS level (e.g. `sudo ip link set eth0 down`) before a short test run and confirm the guard still denies network-related commands; re-enable after the check.

The claim is "guard denies network tooling"; a full airgap is not required unless you enforce it operationally.

## Required

- **Docker**: Running and available. SWE-bench harness evaluation uses Docker to run instance environments.
- **git**: Available on `PATH` (clone, checkout, diff).
- **Python environment** (from repository root or a venv):
  - `datasets` – HuggingFace datasets (loading SWE-bench Lite).
  - `swebench` – SWE-bench harness for evaluation (`python -m swebench.harness.run_evaluation`).
- **OpenHands** (for agent runs): Install if you run real agent-based baseline/PF runs. If you only run eval on existing predictions or use a stub, OpenHands is optional.

## Disk

- Ensure enough free disk for:
  - Docker images and containers used by the SWE-bench harness.
  - HuggingFace dataset cache (SWE-bench Lite).
  - Workspaces and run dirs: `workspaces/`, `runs/exp_step2_lite_smoke/` (evidence, summaries, eval logs).

## Manifest pinning

After filling the manifest, confirm:

- `seed` = 42
- `model_params.temperature` = 0
- `policy_pack` = swebench_safe_v1
- `budgets`: `max_steps` and `timeout_sec` in manifest are used as runner defaults when you pass `--experiment-dir`; override with `--openhands-max-iterations` / `--openhands-timeout` if needed. See `manifest.json` and `commands.md`.
