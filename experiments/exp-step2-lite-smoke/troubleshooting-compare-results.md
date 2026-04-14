# Interpreting low solve rates and compare gate failures (Step 2)

This note explains common outcomes from **compare.json** / **compare.csv** and the **`--require-patch-apply`** gate, and what the repo changed to reduce them.

## What your run showed (typical failure mode)

- **Baseline:** about **1 / 20** harness-resolved (`django__django-10914`); several instances with **empty or non-applying** patches.
- **PF:** **0 / 20** resolved in the harness for this run (patches did not pass project tests).
- **`patch_apply.applies_false`:** often **empty patch** in `patch_apply_check.json` (`stderr: "empty patch"`). That is not always a git-apply bug; it usually means the agent produced **no diff** or the runner recorded an empty patch after timeout or apply-check failure.
- **`compare_runs --require-patch-apply`:** fails when **any** instance has a non-applying patch in the aggregate. Empty patches count as `applies_false`. Omit that flag for a diagnostic compare (you already did); keep it for **golden / parity** runs once patches are healthy.
- **Replay sample size 0:** expected when **no PF instance is harness-resolved**; replay only samples resolved PF cases with clean compliance.

## Root causes (addressed in code / config)

### 1. Task text truncated (~1.8k characters)

The OpenHands subprocess path wrote the full task to a file but still **capped** length at **1800** chars by default. Many SWE-bench Lite instances ship **3k–11k** chars of problem text. The agent often saw a truncated instruction and timed out or produced nothing useful.

**Fix:** default **PF_OPENHANDS_MAX_TASK_CHARS** raised to **12000** in `bench/swebench/engines/openhands_engine.py`. Override with env if tmux/OpenHands errors return.

### 2. Agent time budget vs manifest

Manifest had **timeout_sec 750** while the cycle script defaulted **OPENHANDS_TIMEOUT=900**. Many instances still hit **900s** timeouts in logs.

**Fix:** manifest **timeout_sec** set to **1200**, **max_steps** to **35**; cycle script default **OPENHANDS_TIMEOUT** set to **1200** so CLI and manifest align unless you override.

### 3. Missing `cost_report.json` (no tokens in compare)

When the runner is started as **`python bench/swebench/runner.py`**, `sys.path` is **`bench/swebench`**, not the repo root. **`cost_report.py`** imported **`bench.swebench.constants`**, which failed, so **`build_cost_report`** stayed **None** and **no per-instance cost files** were written. **summary.json** still listed instances with zeros.

**Fix:** **`cost_report.py`** now falls back to **`from constants import ...`** when the absolute package import fails.

### 4. Harness 409 Docker container name conflict

**Signature:** Harness or Docker reports **409** / **name already in use** for a container whose name contains **`sweb.eval`** and your **`run_id`**.

A crashed or partial harness can leave containers named like **`sweb.eval.<instance_id>.<run_id>`**. The next run reuses the same naming pattern and collides.

**Fix (deterministic):** Run the harness wrapper with **`--rm-stale-eval-containers`** (the cycle script passes this before Phase 4.1). Cleanup only removes containers that match **`name=sweb.eval`** in **`docker ps`** and whose **final dot-separated name segment equals the `run_id`** you pass in, so unrelated containers are not removed.

**Manual recovery:**

```bash
docker ps -a --filter name=sweb.eval --format '{{.ID}}\t{{.Names}}'
# Remove lines where the name ends with .<your_run_id>
docker rm -f <container_id>
```

## What you should do next

1. **Re-run agent phase** (baseline + PF) with the updated engine default and manifest so new runs get full task text and longer timeouts (or set env explicitly). Use **`--skip-existing`** only if you intend to keep old instance rows; for a clean comparison prefer new run IDs or a fresh `--out` / `--runs-dir`.
2. **Re-run harness** with **`--rm-stale-eval-containers`** (or use the updated cycle script).
3. **Compare** without **`--require-patch-apply`** for diagnostics; add it back when **`applies_false == 0`** for a golden record.

## References

- `bench/swebench/README.md` — env vars and OpenHands behavior.
- `docs/internal/swebench-stabilization-regression-matrix.md` — pytest gate for provider routing, eval cleanup, compare strict flags, and timeout alignment.
- `experiments/exp-step2-lite-smoke/openhands-headless-troubleshooting.md` — empty trajectory / MessageEvent-only runs and Prime vs OpenAI auth errors.
- `docs/internal/pf-solve-rate-debugging.md` — regression order when baseline and PF diverge.
