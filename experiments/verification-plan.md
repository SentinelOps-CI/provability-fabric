# Verification: Golden Step-2 plan implementation

This document verifies that each item from the "Golden Step-2 parity cycle" plan is implemented and where a skeptical reviewer can check it.

---

## Golden evidence bundle (current implementation)

- **0.0 One-time prep:** golden-cycle.md 0.0: `check_wsl_env.py`, `docker info`, `pf --help`, deps check. Hard rule: if any fail, fix environment first.
- **0.1 Canonical cycle:** golden-cycle.md 0.1: `run-baseline-pf-cycle.sh --update-run-ids`. Produces predictions, eval, compare, run-ids.md (script only), publish/ (GOLDEN.ok, RESULTS.md, PUBLISH.md, VERIFY.md, metadata.yaml, all_preds.jsonl, logs/, trajs/).
- **0.2 Verify gates:** golden-cycle.md 0.3. On failure: **experiments/regression-loop.md**.
- **1.1 VERIFY.md:** update_run_ids_if_green.py writes publish/VERIFY.md (command, run IDs/commits, harness/replay paths, gates).
- **1.2 Machine verifier:** experiments/scripts/verify_publish_bundle.py; fixture experiments/fixtures/verify_publish_bundle/; CI .github/workflows/verify-publish-bundle.yaml.
- **2 Regression loop:** experiments/regression-loop.md (2.1 swebench-regressions, 2.2 fix order, 2.3 rerun slice).
- **3.3 Scale Results Ledger:** append_scale_results_ledger.py, scale-results-ledger.jsonl, scale-results-ledger.md; script appends on green.
- **4.1 Stress alerting:** bench-swebench-stress-scheduled.yaml fails job when parity/timeout/empty_patch/guard_overhead exceed thresholds.
- **4.2 Stress schema + artifact:** stress_summary has schema_version, pf_commit, agent_commit, dataset_id, dataset_version, harness_id; workflow uploads artifact **stress-summary**.

**Local verification (no WSL):** `python experiments/scripts/run_verification_tests.py`.

---

## Top-level conditions (all must be true)

| Condition | Status | Where to verify |
|-----------|--------|------------------|
| baseline.solve_rate and pf.solve_rate numeric (harness ran) | Implemented | compare_runs aggregates from harness reports; golden-cycle.md 0.3 requires "compare.json: baseline.solve_rate and pf.solve_rate are numbers". |
| patch_apply.applies_false == 0 | Implemented | Same doc; script runs compare with --require-patch-apply; update_run_ids_if_green only runs after compare passes. |
| check_no_stub, validate_pf_run, --require-harness --require-compliance --require-patch-apply all pass | Implemented | update_run_ids_if_green.py runs validate_predictions (both), check_no_stub, validate_pf_run, then compare_runs with those three flags (lines 88-106). run-baseline-pf-cycle.sh Phase 4.3 calls compare with all three. |
| RUN IDs recorded only via update_run_ids_if_green.py | Implemented | Script is the only writer of run-ids.md (exp_dir/run-ids.md). Shell passes --experiment-dir experiments/exp-step2-lite-smoke so run-ids.md is written to experiments/exp-step2-lite-smoke/run-ids.md (per GOLDEN_CYCLE). |
| Run bundle is exportable | Implemented | update_run_ids_if_green runs export_publish_artifacts after gates pass; publish dir gets metadata.yaml, all_preds.jsonl, logs/, trajs/, PUBLISH.md, GOLDEN.ok, RESULTS.md, VERIFY.md. Appends to scale-results-ledger.jsonl on green. |

---

## Replay is part of the claim

| Item | Status | Where to verify |
|------|--------|------------------|
| Replay success rate reported | Implemented | run_replay_sample.py writes replay_summary.json (sample_size, success_rate, mismatch_count, replay_fail_reasons_topN). compare_runs merges it into compare.json "replay" section. PUBLISH.md and RESULTS.md include replay summary. |
| Mismatches explainable/rare | Implemented | replay_fail_reasons_topN in replay_summary.json; replay/instance_results.jsonl per instance (failure_reason, match, patch hashes). |

---

## Regression detection is real

| Item | Status | Where to verify |
|------|--------|------------------|
| Scheduled stress run produces stable summary artifact | Implemented | .github/workflows/bench-swebench-stress-scheduled.yaml runs compare then summarize_stress_run.py. |
| Timeout rate and wall-clock summary | Implemented | summarize_stress_run.py outputs stress_summary.json with timeout_rate_baseline, timeout_rate_pf, wall_clock_s_median_baseline/pf, wall_clock_s_p95_baseline/pf, guard_overhead_s_median, plus solve rates and empty_patch_reasons_topN. |
| Schema versioning and provenance | Implemented | stress_summary.schema.json includes schema_version, pf_commit, agent_commit, dataset_id, dataset_version, harness_id. summarize_stress_run.py writes them (--pf-commit; others from compare.json). |
| Named artifact and regression alerting | Implemented | Workflow uploads stress_summary.json as artifact **stress-summary**. "Stress regression alerts" step fails job when parity, timeout delta, empty_patch rate, or guard_overhead exceed thresholds. |
| Detect "PF makes hard repos worse" over time | Implemented | Diff stress_summary.json across runs; use scale-results-ledger.jsonl for cumulative per-experiment rows. |

---

## Phase 0 — First golden Step-2 run

### 0.1 Run the golden cycle on WSL/Linux

| Output | Status | Location / note |
|--------|--------|------------------|
| Canonical command | Documented | golden-cycle.md 0.1: `bash experiments/scripts/run-baseline-pf-cycle.sh --update-run-ids` |
| runs/exp-step2-lite-smoke/baseline/predictions.jsonl | From pipeline | Shell writes baseline predictions to BASELINE_DIR (EXP/baseline). |
| runs/exp-step2-lite-smoke/pf/predictions.jsonl | From pipeline | Shell writes PF predictions to PF_DIR (EXP/pf). |
| runs/exp-step2-lite-smoke/baseline/eval/* and pf/eval/* | From pipeline | run_swebench_eval.py Phase 4.1 writes to baseline/eval and pf/eval. |
| runs/exp-step2-lite-smoke/compare.json and compare.csv | From pipeline | compare_runs.py Phase 4.3 with --experiment-dir "$EXP" writes to out_dir (EXP). |
| run-ids.md updated by script | Implemented | update_run_ids_if_green.py writes exp_dir/run-ids.md when all gates pass. Shell passes --experiment-dir experiments/exp-step2-lite-smoke so file is experiments/exp-step2-lite-smoke/run-ids.md. |

### 0.2 Freeze what "golden" means (evidence file)

| Field | Status | Where |
|-------|--------|-------|
| baseline_run_id, pf_run_id | Implemented | golden-cycle.md "0.5 Human-facing notarization" table; GOLDEN.ok (machine-readable). |
| pf_commit, agent_commit/image_tag | Implemented | Same table; GOLDEN.ok has pf_commit; agent from env.json documented. |
| dataset_name + harness_dataset_id, swebench/datasets versions | Implemented | Table: from compare.json or eval_metadata.json. |
| Replay sample size and replay success rate | Implemented | Table: replay.sample_size, replay.success_rate from compare.json. |

### 0.3 Golden stamp file

| Item | Status | Where to verify |
|------|--------|------------------|
| GOLDEN.ok on success (after export) | Implemented | update_run_ids_if_green.py after export writes publish_dir/GOLDEN.ok. |
| Contents: run IDs + commit + timestamp + parity gate | Implemented | JSON: baseline_run_id, pf_run_id, pf_commit, timestamp_utc, parity_gate_passed. |
| VERIFY.md for reviewer audit | Implemented | Same script writes publish/VERIFY.md (command, run IDs/commits, harness/replay paths, gates). Machine verifier: verify_publish_bundle.py. |

**Acceptance gate Phase 0:** golden-cycle.md describes the pipeline and acceptance checks; a new engineer can follow it to reproduce structure and gating (0.1 run is human-executed on WSL/Linux). If any gate fails, follow **experiments/regression-loop.md**.

---

## Phase 1 — Stress summary timeout + wall-clock

### 1.1 Define "timeout" operationally

| Item | Status | Where to verify |
|------|--------|------------------|
| timeout := runner marked or OpenHands budget exhaustion | Implemented | bench/swebench/README.md: "timeout := runner set timeout_reached true (TimeoutExpired) or termination_reason == \"max_steps\"". |
| Kept separate from guard_denial, etc. | Implemented | runner.py termination_reason enum: timeout, max_steps, guard_denial, empty_patch, error, success. |

### 1.2 Per-instance timing + termination reason

| Item | Status | Where to verify |
|------|--------|------------------|
| timing.json per instance | Implemented | bench/swebench/runner.py writes inst_dir/TIMING_JSON_FILENAME after cost_report (constants.TIMING_JSON_FILENAME = "timing.json"). |
| wall_clock_s, tool_calls | Implemented | timing dict has wall_clock_s, tool_calls, max_steps_reached, timeout_reached, termination_reason. |
| max_steps_reached / timeout_reached / termination_reason | Implemented | Same block in runner.py. |

### 1.3 Aggregator script summarize_stress_run.py

| Item | Status | Where to verify |
|------|--------|------------------|
| Inputs: baseline run dir, PF run dir, compare.json | Implemented | experiments/scripts/summarize_stress_run.py --baseline-run-dir, --pf-run-dir, --compare-json. |
| Outputs: stress_summary.json with timeout_rate_*, wall_clock_s_median_*, p95_*, guard_overhead_s_median, empty_patch_reasons_topN, patch_apply, solve rates | Implemented | Script builds stress dict with all these keys; writes to --out. |

### 1.4 Schema + unit test

| Item | Status | Where to verify |
|------|--------|------------------|
| stress_summary.schema.json | Implemented | experiments/schemas/stress_summary.schema.json. |
| Unit test with synthetic run dirs | Implemented | tests/test_summarize_stress_run.py (two tests: valid summary with timing, timeout_rate from timing.json). |

### 1.5 Wire into bench-swebench-stress-scheduled.yaml

| Item | Status | Where to verify |
|------|--------|------------------|
| After compare, run summarize_stress_run.py --out stress_summary.json | Implemented | .github/workflows/bench-swebench-stress-scheduled.yaml "Write stress summary" step calls summarize_stress_run.py with baseline-run-dir, pf-run-dir, compare-json, --out "$EXP/stress_summary.json". |

---

## Phase 2 — Security + reliability claim

### 2.1 Replay coverage representative

| Item | Status | Where to verify |
|------|--------|------------------|
| Replay all PF-resolved violations==0 when count <= 20 | Implemented | run_replay_sample.py --replay-all-if-le 20; if len(candidates) <= args.replay_all_if_le then sample = sorted(candidates). |
| Otherwise deterministic sample (seed) 25-50 | Implemented | else branch: size = min(len(candidates), max(25, args.sample_size_scheduled)); rng = random.Random(args.seed); sample = sorted(rng.sample(candidates, size)). Default sample_size_scheduled=40. |
| replay/instance_results.jsonl (patch hashes, match bool, failure reason) | Implemented | run_replay_sample.py writes replay_dir/instance_results.jsonl with instance_id, success, match, replay_ok, original_patch_sha256, reconstituted_patch_sha256, failure_reason. |
| replay_summary.json rollup | Implemented | Unchanged; still written. |

### 2.2 Negative capability (network unavailable)

| Item | Status | Where to verify |
|------|--------|------------------|
| WSL doc: network-unavailable check (curl denied, optional OS network off) | Implemented | experiments/exp-step2-lite-smoke/env-checklist.md "Network-unavailable (negative capability)" section: verify curl/wget/pip+URL denied in compliance; optional OS-level network disable. |

### 2.3 Denial recovery metrics

| Item | Status | Where to verify |
|------|--------|------------------|
| denials_total_pf | Implemented | compare_runs.py: out["pf"]["denials_total_pf"]; compare_report.schema.json. |
| episodes_aborted_after_denial_pf | Implemented | compare_runs.py: out["pf"]["episodes_aborted_after_denial_pf"]. |
| recovered_after_denial_pf_rate | Implemented | compare_runs.py: out["pf"]["recovered_after_denial_pf_rate"]; schema. |

---

## Phase 3 — Scale and institutionalize

### 3.1 Expand coverage (medium 50, fullish 200)

| Item | Status | Where to verify |
|------|--------|------------------|
| exp-step2-lite-medium-50 | Implemented | experiments/exp-step2-lite-medium-50/README.md, manifest.json; 50 instances, seed 42, same manifest discipline. |
| exp-step2-lite-fullish-200 | Implemented | experiments/exp-step2-lite-fullish-200/README.md, manifest.json; 200 instances. |
| Same harness + compare gates + replay reporting | Documented | READMEs reference same pipeline and gates. |

### 3.2 Triage-to-fix cadence (make swebench-regressions)

| Item | Status | Where to verify |
|------|--------|------------------|
| Single target consuming baseline_solved_pf_failed.txt | Implemented | Makefile target swebench-regressions: requires BASELINE_RUN_DIR, PF_RUN_DIR; runs list_delta_cases, extract_case_bundle (from analysis/baseline_solved_pf_failed.txt), bucket_pf_failures_from_cases; full loop: **experiments/regression-loop.md**. |

### 3.3 Public claim threshold (acceptance gates by scale)

| Item | Status | Where to verify |
|------|--------|------------------|
| Max acceptable drop and max acceptable increase in timeouts/empty patches | Implemented | experiments/README.md "Acceptance gates by scale": parity gate and max drop (0.01 smoke, 0.02 medium, 0.03 fullish); max increase in timeouts/empty-patch rate; document in experiment README. exp-step2-lite-medium-50/README.md and exp-step2-lite-fullish-200/README.md have "Acceptance gates by scale" with numeric thresholds. |

---

## Phase 4 — Package like a benchmark submission

### 4.1 RESULTS.md and VERIFY.md (generated)

| Item | Status | Where to verify |
|------|--------|------------------|
| update_run_ids_if_green.py writes publish/RESULTS.md | Implemented | update_run_ids_if_green.py: run IDs, solve rates + delta, patch_apply parity, violations summary, replay summary, env drift, artifact layout. |
| publish/VERIFY.md and machine verifier | Implemented | Same script writes VERIFY.md. Verifier: experiments/scripts/verify_publish_bundle.py; CI: .github/workflows/verify-publish-bundle.yaml. |

### 4.2 Publish bundle integrity (MANIFEST.sha256)

| Item | Status | Where to verify |
|------|--------|------------------|
| SHA-256 manifest of all files under `publish/` | Implemented | `experiments/scripts/publish_manifest.py`; `update_run_ids_if_green.py` calls `write_publish_manifest_sha256` after VERIFY.md. |
| Verifier checks hashes | Implemented | `verify_publish_bundle.py` uses `verify_publish_manifest_sha256`. CI: verify-publish-bundle workflow. |
| Optional GPG/sigstore signature on manifest | Not implemented | Future step; manifest file is the tamper-evident base layer. |

---

## Summary

All planned items are implemented except:

1. **Phase 0.1** is a one-time human action: run the golden cycle on WSL/Linux and verify the listed outputs exist (use `PF_REQUIRE_NONZERO_SOLVE=1` on the cycle script after agent fixes to require positive solve rates).
2. **Optional cryptographic signature** on `MANIFEST.sha256` (GPG/sigstore) is not implemented.

**Current state:** VERIFY.md, verify_publish_bundle.py, regression-loop.md, Scale Results Ledger (with **experiments/schemas/scale_results_ledger_row.schema.json**; rows validated before append), stress schema versioning and named artifact **stress-summary**, stress alerting (**check_stress_alerts.py**; thresholds in **experiments/config/stress_alerts.yaml**, optional), and run_verification_tests.py are in place. **Shared modules:** **publish_docs.py** (build_publish_md, build_results_md, build_verify_md) generates PUBLISH.md, RESULTS.md, VERIFY.md; **publish_bundle.py** defines required publish files/dirs and GOLDEN.ok keys (used by verifier and export); **compare_gates.py** centralizes compare.json gate checks. A reviewer can clone the repo, open this file and the cited paths, and confirm each "Where to verify" entry.
