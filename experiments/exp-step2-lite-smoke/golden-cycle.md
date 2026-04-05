# Golden Step-2 cycle and freeze

This document defines the **one trusted reference run** (baseline + PF pair) where all gates pass. Do not change documentation to paper over failures; fix the pipeline until the golden cycle passes, then freeze run-ids via the script only.

## 0.0 One-time WSL/Linux prep (do not skip)

Run these from repo root in WSL/Linux and capture outputs (copy/paste into a `runs/exp_step2_lite_smoke/publish/` section or attach as logs):

```bash
python experiments/scripts/check_wsl_env.py
docker info
pf --help
# Or confirm fallback: python bench/swebench/runner.py --help
python -c "import openhands, datasets, swebench; print('deps ok')"
```

**Hard rule:** If any of these fail, fix the environment first. Do not "try a run anyway."

## 0.1 Run the canonical pipeline (WSL/Linux only)

From repository root:

```bash
bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids
```

This runs: strict env check (`check_wsl_env.py --strict-linux`), manifest fill, resolved model + provider (`resolve_cycle_llm.py`, explicit `--openhands-model` on runs), baseline run, PF run, validations, harness, compare with harness/compliance/patch-apply/**priced-models** gates, then **update_run_ids_if_green.py** (writes **compare.json** and **metrics_full.json** under **runs/exp-step2-lite-smoke/**, optional **PF_GPG_SIGN_MANIFEST** on **MANIFEST.sha256**).

## 0.2 Artifacts you must be able to point to

After a successful run, these paths must exist and be consistent:

| Artifact | Path |
|----------|------|
| Baseline predictions | `runs/exp_step2_lite_smoke/baseline/predictions.jsonl` |
| PF predictions | `runs/exp_step2_lite_smoke/pf/predictions.jsonl` |
| Baseline eval | `runs/exp_step2_lite_smoke/baseline/eval/` (harness report + eval_metadata.json) |
| PF eval | `runs/exp_step2_lite_smoke/pf/eval/` (harness report + eval_metadata.json) |
| Compare report | `runs/exp_step2_lite_smoke/compare.json`, `compare.csv`, and **`metrics_full.json`** (run card: solve rates, harness test runtime per instance, agent latency summary, cost estimate, version pins) |
| Harness test runtime | In **`compare.json` → `harness_eval`**: per-instance seconds parsed from `eval/logs/run_evaluation/.../run_instance.log` (`Test runtime: N seconds`; test phase only, not agent wall-clock) |
| run-ids.md | `experiments/exp_step2_lite_smoke/run-ids.md` **updated by the script only (not manually)** |
| Publish bundle | `runs/exp_step2_lite_smoke/publish/` including GOLDEN.ok, RESULTS.md, PUBLISH.md, metadata.yaml, all_preds.jsonl, logs/, trajs/ |

## 0.3 Verify gates (release checklist)

Open `runs/exp_step2_lite_smoke/compare.json` and assert:

- `baseline.solve_rate` is a number (not null).
- `pf.solve_rate` is a number (not null).
- `patch_apply.applies_false == 0`.
- `budget_drift` is absent or empty (and the run did not exit nonzero).
- **policy** section exists and is non-empty (reason_codes / deny stats).
- **replay** section exists (sample_size, success_rate, mismatch_count).

Assert these files exist in the publish bundle:

- `publish/all_preds.jsonl`
- `publish/logs/<instance_id>/` for multiple instances
- `publish/trajs/<instance_id>.json` for multiple instances
- `publish/GOLDEN.ok`

If any one gate fails: do not write "golden" anywhere; go straight into the regression loop (**experiments/regression-loop.md**).

## 0.4 Acceptance checks (hard)

Before considering the run "golden", also assert:

1. **validate_pf_run.py** exits 0 for the PF run dir:
   ```bash
   python bench/swebench/validate_pf_run.py runs/exp_step2_lite_smoke/pf/<PF_RUN_ID>
   ```

2. **check_no_stub.py** exits 0:
   ```bash
   python experiments/scripts/check_no_stub.py runs/exp_step2_lite_smoke/baseline runs/exp_step2_lite_smoke/pf
   ```

3. **run-ids.md** was written by `update_run_ids_if_green.py` (script logs "Updated ... with baseline=... pf=...").

4. **Machine verifier:** `python experiments/scripts/verify_publish_bundle.py --publish-dir runs/exp_step2_lite_smoke/publish --compare-json runs/exp_step2_lite_smoke/compare.json --run-ids-md experiments/exp_step2_lite_smoke/run-ids.md` exits 0 (optional but recommended).

If any of these fails on first attempt, **do not change docs**. Fix the pipeline (patch extraction, apply check, guard, or harness) until the golden cycle passes. Everything else (compare, triage, export, stress slice) depends on having one trusted reference run.

## 0.5 Human-facing notarization (freeze what "golden" means)

When you complete a golden run, record the exact values below. This is the human-facing evidence that a skeptical reviewer can verify. Machine-readable equivalents are written by the script to `runs/exp_step2_lite_smoke/publish/GOLDEN.ok` and `publish/RESULTS.md`.

| Field | Value (fill after run) |
|-------|------------------------|
| baseline_run_id | `20260317-120041-1badcd73` (see run-ids.md; update after next green run) |
| pf_run_id | `20260317-143046-340fb140` (see run-ids.md) |
| pf_commit | from `publish/GOLDEN.ok` or `git rev-parse --short=12 HEAD` at export time |
| agent_commit / image_tag | from `runs/.../baseline/<id>/env.json` `openhands_version` when present |
| dataset_name | SWE-bench_Lite (typical; confirm in compare.json) |
| harness_dataset_id | `eval_metadata.json` under `baseline/eval` and `pf/eval` |
| swebench_version | compare.json reproducibility or eval_metadata |
| datasets_version | compare.json reproducibility or eval_metadata |
| replay sample size | 0 until PF has resolved compliant instances; then compare.json |
| replay success_rate | N/A when sample_size=0; then compare.json |

After a re-run with non-zero solves, refresh this table and run `python experiments/scripts/check_golden_solve_rates.py --compare-json runs/exp-step2-lite-smoke/compare.json --require-nonzero`.

## 0.3 Golden stamp (automation)

On success, `update_run_ids_if_green.py` (after export) writes:

- **`runs/exp_step2_lite_smoke/publish/GOLDEN.ok`**  
  Contents: baseline_run_id, pf_run_id, pf_commit, timestamp_utc, parity_gate_passed (JSON). Downstream automation (release workflows, docs pages) can rely on this file to exist only when the full gated cycle passed.

- **`runs/exp_step2_lite_smoke/publish/RESULTS.md`**  
  Audit-friendly summary: run IDs, solve rates, delta, patch_apply parity, violations summary, replay summary, env drift, pointers to logs/trajectories. No marketing—just "how to audit this."

**Phase 4.2 (manifest):** `update_run_ids_if_green.py` writes **`publish/MANIFEST.sha256`** (SHA-256 of every file under `publish/` except the manifest itself). `verify_publish_bundle.py` recomputes hashes and fails on mismatch. **Optional GPG:** set `PF_GPG_SIGN_MANIFEST=1` when running `publish_manifest.py` to emit **`MANIFEST.sha256.asc`** (`gpg --detach-sign`; optional key via `PF_GPG_KEY_ID`). Sigstore remains future work.

**Solve rate and model:** Manifest defaults to **`gpt-4o`** for serious smoke; solve rate is not guaranteed. **`estimated_cost_usd`** in compare is indicative only; extend **`experiments/scripts/model_pricing.py`** if you use a model not in **`USD_PER_1M`**.

**Environment drift:** Long runs can fail on Docker, API, or OpenHands version drift. After a good run, pin **`openhands_version`**, **`datasets_version`**, **`swebench_version`**, and **`pip_freeze_hash`** from each run's **`env.json`** into the experiment manifest.

## Run notes template

When you complete a golden run, record:

- **Date and environment:** e.g. "2026-02-XX, WSL Ubuntu 22.04"
- **Baseline run_id:** from run-ids.md
- **PF run_id:** from run-ids.md
- **Gates passed:** validate_predictions (both, with --allow-empty-patch when run via the cycle), check_no_stub, validate_pf_run, harness reports present, compare with --require-harness --require-compliance --require-patch-apply, patch_apply.applies_false == 0
- **Commit:** git rev-parse HEAD (for reproducibility)
