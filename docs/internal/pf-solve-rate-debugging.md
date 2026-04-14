# PF solve rate debugging and fix strategy

When the PF-guarded solve rate drops vs baseline, categorize each PF-failed instance into exactly one primary cause and apply the fix strategy for that bucket. Do not weaken the security story (network stays off; filesystem confinement stays strict).

**Zero-solve runs:** `compare.json` still carries **per-attempt** metrics even when harness solve_rate is 0: **baseline.cost_per_attempt** / **pf.cost_per_attempt** (avg tokens, wall_clock_s, tool_calls over all instances in the run summary), **latency_per_attempt** and **tokens_per_attempt** (median, p90, p95), **termination_mix** (timeout/max_steps rates), and **estimated_cost_usd** (indicative totals from **experiments/scripts/model_pricing.py**). Use these to compare PF vs baseline cost and latency before any task is solved.

**See also:** Experiment manifest and compare flow: **experiments/README.md**. Exact run, eval, and compare commands: **experiments/exp-step2-lite-smoke/commands.md**; canonical golden run and acceptance criteria: **experiments/exp-step2-lite-smoke/golden-cycle.md**. The compare script (`compare_runs.py`) supports `--require-harness` (run_id consistency, **stale-eval check**, optional predictions_sha256, **budget drift** from experiment_manifest.json), `--require-compliance`, and `--require-patch-apply`; it aggregates `patch_apply_check.json` from both run dirs and emits **empty_patch_reasons_topN** (reason codes: agent_no_changes, patch_too_large, diff_timeout, apply_check_failed, workspace_missing_or_failed, guard_denial_prevented_writes). The compare report also includes **replay** (from replay_summary.json; run_replay_sample writes replay/instance_results.jsonl), **policy** (reason_codes_topN, denied_commands_topN), and **denial recovery** (denials_total_pf, episodes_aborted_after_denial_pf, recovered_after_denial_pf_rate). Per-instance `patch_apply_check.json` and `empty_patch_reason.txt` in each run dir give the exact cause for empty patches. For parity, `patch_apply.applies_false` must be 0 (enforce with `--require-patch-apply`). Update **RUN_IDS.md** only after all gates pass via **experiments/scripts/update_run_ids_if_green.py** (which also runs export and writes **publish/PUBLISH.md**, **publish/GOLDEN.ok**, **publish/RESULTS.md**); RUN_IDS.md lives in **experiments/exp-step2-lite-smoke/RUN_IDS.md**.

## Concrete iteration workflow

Use this order every time: identify baseline-solved / PF-failed, extract artifacts, apply fixes in leverage order, rerun until solve delta is acceptable and PF final-patch violation rate is near zero.

### 1. Identify "baseline solved, PF failed"

From `compare.csv` (output of `compare_runs.py`), filter:

- `baseline_resolved` = 1 (or true)
- `pf_resolved` = 0 (or false)

If `compare.csv` has no per-instance rows (e.g. harness not run yet), the extraction script can fall back to harness reports in `baseline/eval` and `pf/eval` to compute the same set.

### 2. Extract artifacts per instance

For each such instance, collect:

- **PF `policy_compliance_summary.json`** (from PF run dir)
- **Top 20 lines around the first violation** in `evidence/events.jsonl`
- **Last ~50 lines of OpenHands trace** (e.g. `run.log`)

Run:

```bash
python experiments/scripts/extract_baseline_solved_pf_failed.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id> \
  --out-dir runs/exp-step2-lite-smoke/debug_baseline_solved_pf_failed
```

Output: `<out-dir>/<instance_id>/policy_compliance_summary.json`, `events_first_violation_context.txt`, `run_log_tail.txt`, and `instance_ids.txt` listing all such instances.

### 3. Apply fixes in order (highest leverage first)

| Order | Fix | Action |
|-------|-----|--------|
| **1** | **Agent recovery on denial** | If denials are recoverable but OpenHands stops anyway, adjust the OpenHands engine wrapper so the denial return code is treated as "command failed, continue planning" rather than aborting the episode. |
| **2** | **Policy allowlist for local tooling only** | Add missing local commands (e.g. `python -m pytest`, `python -m pip`, `git`, `grep`, `sed`). Do not enable network. |
| **3** | **Budget tuning** | PF overhead can push runs into timeouts. Increase timeout slightly (e.g. +15–25%) while keeping the same max iterations, or cap tool calls more aggressively to reduce thrash. |
| **4** | **Patch extraction correctness** | The runner now runs `git apply --check --whitespace=nowarn` per instance and writes `patch_apply_check.json`; if the patch does not apply, it emits an empty patch for that instance. For manual checks: run `git apply --check model.patch` inside a clean checkout at base commit. |

### 4. Rerun until criteria are met

After each fix, rerun the same 20-instance slice (same `instance_ids.txt`, same manifest seed/temperature). Run harness eval and compare (see **experiments/exp-step2-lite-smoke/commands.md** Case 1.3 and 1.4). Check: **solve delta** is acceptable and **PF final-patch violation rate** is near zero. Repeat from step 1 (identify remaining baseline-solved / PF-failed) until both conditions hold.

---

## Fix loop per bucket (without weakening security)

This is where most "PF parity" projects succeed or die. The rule: **expand capability only when you can justify it as local, deterministic, and auditable.**

### Bucket A: policy_denial_or_violation

**Typical causes (and the safe fixes):**

- **Local tooling blocked** (e.g. `python -m pytest`, `pip install -e .`, `make test`).
  - Add to allowlist: `python`, `python3`, `pytest`, `pip`, `make`, `gcc`/`g++` (if needed), `cargo` (if repo is Rust), etc.
  - Enforce no network by arguments too: deny any command that contains `http://`, `https://`, `git+`, `ssh://`, or `@github.com`.
- **Agent cannot recover from a denial.**
  - Update the OpenHands system/task framing to explicitly instruct: "If a command is denied (exit 125), do not retry; choose a permitted alternative." "Never attempt network; assume offline."
- **Write-path false positives** (guard thinks you wrote outside workspace).
  - Improve the path parser to correctly detect `-o`, `--output`, redirections, etc., but keep the policy: writes must be under workspace.

**Non-negotiable acceptance tests for policy changes:**

- Deny `curl example.com` (reason_code `binary_forbidden`).
- Deny `pip install requests` if it includes any URL / VCS dependency hint.
- Allow `python -m pytest` and `pip install -e .` (offline local install).

### Bucket B: patch_format_or_apply

This is almost always a runner/patch extraction issue (not "model quality"):

- Emit unified diffs with correct `a/` and `b/` paths, and final newline.
- Generate patch from `git diff HEAD` in the workspace repo root.

**Acceptance test:** Take a known solved instance, run `git apply --check model.patch` inside a clean checkout at base commit.

### Bucket C: budget_timeout

- Do not silently "give PF more budget." Make budgets identical baseline vs PF.
- If PF adds overhead (guard + evidence writes), measure it explicitly and raise timeout for **both** modes equally.
- Add a column in summary: `guard_overhead_s = wall_clock_s_pf - wall_clock_s_baseline` (median across instances).

### Bucket D: agent_quality_or_missing_tooling

If you see this bucket with zero violations, PF probably is not the culprit; it is noise.

- Confirm determinism: temperature=0; fixed seed; same OpenHands version; same runtime.
- If it persists, reduce variance by running each instance k=3 and using best-of-3 for **both** modes (keep it symmetric).

---

## A. Five failure buckets

For each instance that **baseline resolved but PF did not**, assign exactly one primary cause:

| Bucket | Description |
|--------|-------------|
| **policy_too_strict** | Policy is denying benign actions needed for SWE-bench-style fixing (e.g. local pytest, pip install -e ., make, ruff). |
| **agent_not_adapting** | Denials are clear (e.g. network); agent should have revised plan or used local alternatives but did not. |
| **runner_integration_bug** | Workspace, patch extraction, or tool gateway bug (e.g. patch apply failed in harness, git state mismatch). |
| **budget_regression** | PF overhead causes timeouts; same budget no longer enough. |
| **stochasticity** | Should not happen with seed/temp=0; investigate non-determinism. |

### Categorization script

Run after you have baseline and PF harness eval plus PF run evidence:

```bash
python experiments/scripts/categorize_pf_failures.py \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --pf-run-dir runs/exp-step2-lite-smoke/pf/<pf_run_id>
```

Outputs: `pf_failure_categories.json` and `pf_failure_categories.csv` with `instance_id`, `primary_cause`, and `details`. Use bucket counts to prioritize fixes.

---

## B. Fix strategy per bucket

### (1) Policy too strict

- **Do not** "open network."
- **Do:**
  - Expand **allowlist** for local tooling only: e.g. `python -m pytest`, `ruff`, `make`, `pip install -e .` (offline install). The guard allowlist already includes `pip`, `make`, `ruff`, `nox`, `tox`, `coverage`, `black`, `mypy`.
  - Allow reading additional repo files the agent needs (if path rules block legitimate in-repo paths, relax only for paths under workspace).
  - Keep **filesystem confinement** strict: no writes outside workspace; no `/etc`, `/tmp`, `/home` etc.

### (2) Agent not adapting

- Ensure denial errors are **structured and actionable**:
  - Format: `DENIED: reason=<code>; suggestion=<text>; message=<detail>`
  - Example: `reason=NETWORK_DISABLED` (or `binary_forbidden`) with `suggestion=use_local_docs;` or "Network is unavailable; do not attempt external fetch."
- In the agent prompt/system message:
  - "Network is unavailable; do not attempt external fetch."
  - "If a command is denied, revise plan and proceed."
- The guard executor already emits `DENIED: reason=...; suggestion=...;` and suggestions are defined in `bench/swebench/guard/tool_gateway.py` (e.g. for `binary_forbidden`: "Network is unavailable; do not attempt external fetch. Use local docs, pip install -e ., or offline tools."). Wire these into the agent instructions.

### (3) Runner integration bug

- Common causes: patch extraction mismatches git state; newline normalization; wrong base commit.
- Add an explicit **"apply patch + git diff sanity check"** step before writing predictions (e.g. in runner or in a pre-submit check).
- Fix workspace materialization or tool gateway so that patch apply in the harness matches the agent’s view of the repo.

### (4) Budget regression

- PF adds overhead (logging + enforcement). Compensate by:
  - Increasing **wall-clock timeout** slightly, or
  - Reducing agent iteration steps while keeping overall compute similar.
- Keep a **strict budget policy**; only tune it so that PF runs complete within budget.

### (5) Stochasticity

- Force **temperature=0**, deterministic tool ordering, **fixed seed**.
- Record exact prompts (and any non-determinism) to reproduce.
- Re-run the same 20-instance slice after each change to confirm.

---

## C. Replay validation (after fixes)

Run replay **only** for instances that:

1. **PF solved** (harness says resolved), and  
2. Had **zero policy violations** on the final run (compliant in `policy_compliance_summary.json`).

Replay in deterministic mode:

```bash
pf bench swebench replay \
  --run_id <run_id> \
  --instance_ids <id1>,<id2>,<id3> \
  --runs-dir runs \
  --json
```

Or with Python directly:

```bash
python bench/swebench/run_replay.py \
  --run-id <run_id> \
  --instance-ids id1,id2,id3 \
  --runs-dir runs \
  --json
```

### Pass criteria

- **Patch hash matches original**: `original_patch_sha256` equals `reconstituted_patch_sha256` for each instance.
- **Tool trace replays without divergence**: Replay applies file_edits and reconstitutes patch; no model call.
- **`replay_ok`: true** in the JSON report (per result: `replay_ok` = `success` and `match`; top-level `replay_ok` = all instances pass).

If replay fails, fix replay before claiming "reliable/security-by-design"; replay is core to the story.

### Selecting instances for replay

From the PF run dir and compliance summaries, collect instance IDs where:

- Harness report has the instance in `resolved_ids`, and  
- `policy_compliance_summary.json` for that instance has `compliant: true` and `violations: 0`.

Then run:

```bash
pf bench swebench replay --run_id <pf_run_id> --instance_ids id1,id2,id3 --json
```

Inspect `replay_ok` and each result’s `match` and `message`.
