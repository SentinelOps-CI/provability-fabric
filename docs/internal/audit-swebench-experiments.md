# Audit report: SWE-bench and experiments

**Date:** 2026-02-13  
**Scope (repo commit):** 819caccf  
**Scope (in scope only):** bench/swebench (Python runner, loader, workspace, engines, replay, guard, policy, constants, util, validate_pf_run, cost_report, proof_hook, fixtures, schemas); experiments/ (README, exp-step2-lite-smoke, all scripts under experiments/scripts/); PF CLI swebench run/replay; CI bench-swebench-smoke and bench-swebench-unit. **Out of scope:** Criterion/Rust bench, other workflows, runtime sidecar, Lean proofs.

**Remediation (post-audit):** CLI now exposes `--openhands-max-iterations`; atomic predictions (write to `.tmp`, rename on success) and `run_status.json` in the same directory as predictions; `validate_predictions --allow-partial`; synthetic fixture generator and unit tests for compare_runs, validate_predictions, check_no_stub, validate_pf_run, loader, workspace, replay placeholder; CI workflow `.github/workflows/bench-swebench-unit.yaml` (ubuntu + windows); JSON schemas `experiments/schemas/compare_report.schema.json` and `harness_report_min.schema.json` with optional validation in compare_runs; `update_run_ids_if_green.py` (update run-ids.md only when all gates pass); `env.json` in each run dir and `env_drift` in compare.json; WSL doc (build pf, PATH) and script fallback when pf not on PATH.

---

## Summary

| Dimension | Result | Note |
|-----------|--------|------|
| 1. Documentation vs implementation | Pass | CLI passes --openhands-max-iterations (0 = use manifest/default); COMMANDS uses --dataset lite (accepted); "Without pf CLI" and run-baseline-pf-cycle.sh fallback when pf absent. |
| 2. Testing | Pass | Runner smoke + unit tests for compare_runs, validate_predictions, check_no_stub, validate_pf_run, loader, workspace (mocked), replay placeholder; fixture generator; CI bench-swebench-unit.yaml. |
| 3. Error handling | Pass | Atomic predictions; run_status.json (complete/partial/failed); validate_predictions --allow-partial; partial run behavior documented. |
| 4. Schema and contracts | Pass | compare_report.schema.json, harness_report_min.schema.json; compare_runs validates with jsonschema when installed. |
| 5. Security and credentials | Pass | No keys in code; .env gitignored; sanitize_instance_id used for paths. |
| 6. Reproducibility | Pass | Seed and manifest documented; `run-ids.md` updated only via update_run_ids_if_green.py when gates pass; env.json + env_drift for baseline vs PF. |
| 7. Technical debt | Addressed | Two entry points documented in README (Entry points section); engine tuning constants moved to bench/swebench/constants.py (single source of truth, optional PF_* env overrides); run_evidence and compare_runs share constants. |
| 8. Experiments workflow | Pass | COMMANDS order correct; update_run_ids_if_green.py canonical; WSL/Windows and pf fallback documented. |
| 9. Edge cases and claims | Pass | Empty vs stub clarified; preflight does not guarantee full-run success; run_status and --allow-partial documented. |

**Remaining risks:** (1) Harness or compare run against wrong run_id or eval dir layout (mitigated by gates and update_run_ids_if_green). (2) Dataset or OpenHands version drift (env.json and env_drift surface differences; reproducibility and version-pinning guidance in bench/swebench/README.md and experiments/README.md, env-checklist.md). (3) Large repos still produce empty patches despite path-restricted logic (Known limitations section in bench/swebench/README.md; preflight documented as not guaranteeing full-run success).

---

## 1. Documentation vs implementation (truthfulness)

| Claim (doc quote) | Code/location | Pass/Fail | Note |
|-------------------|---------------|-----------|------|
| "pf bench swebench run --dataset Lite" | `run_config.RunConfig.__post_init__` normalizes dataset names to Lite, Verified, Full | Pass | Both Lite and lite accepted. |
| commands.md "--dataset lite" | same | Pass | lite -> Lite. |
| "Budgets from manifest" when --experiment-dir set | `run_config.RunConfig._apply_manifest_budgets` | Pass | max_steps, timeout_sec applied to openhands_max_iterations, openhands_timeout when CLI flags were not explicitly passed. |
| "Override with --openhands-max-iterations / --openhands-timeout" | runner.py and core/cli/pf/main.go both expose --openhands-max-iterations and --openhands-timeout | Pass | CLI passes --openhands-max-iterations when > 0; 0 = use manifest or runner default. |
| ENV_CHECKLIST: OPENAI_API_KEY, ANTHROPIC_API_KEY, OPENHANDS_API_KEY, OPENAI_BASE_URL | .env loaded by wsl-baseline-pf-cycle.sh | Pass | Documented. |
| PF_GIT_DIFF_TIMEOUT, PF_MAX_PATCH_BYTES | bench/swebench/constants.py, README | Pass | Documented in README. |
| "Without pf CLI" run from `cd bench/swebench && python runner.py" with ../../ paths | commands.md Case 1.1 | Pass | Paths relative to bench/swebench; imports (loader, workspace) resolve when cwd is bench/swebench. |
| Manifest schema (experiment_id, pf_commit, budgets, ...) | experiments/README.md vs manifest.json | Pass | manifest.json has all fields; fill_manifest_from_run writes pf_commit, created_at. |

---

## 2. Testing (coverage and honesty)

| Component | Test exists (Y/N) | If Y, what is asserted | If N, risk |
|-----------|-------------------|------------------------|------------|
| runner.py (`_execute_run` / CLI `main`) | Y | test_swebench_runner_smoke.py: mock engine, no-workspace, guarded mode, violation reason binary_forbidden, predictions.jsonl line count, run dir layout, evidence files | - |
| loader.py | Y | test_loader_from_file.py: load from JSONL, max_instances, instance_ids filter | - |
| workspace.py | Y | test_workspace_plan.py: manifest shape/hash, invalid repo raises, mocked git | - |
| openhands_engine.py | Y | test_openhands_engine.py: _is_like_diff accept/reject, _get_patch_from_repo timeout fallback (skip on Windows), _parse_trajectory missing file returns empty trace, path-restricted diff behavior | - |
| mock_engine.py | Y (indirect) | Via runner smoke: mock produces trace and patch | - |
| replay (replay.py, capture.py) | Y (placeholder) | test_replay_roundtrip.py (skip on Windows) | Full roundtrip optional. |
| guard (executor, pf_guard_exec) | Y (indirect) | Smoke runs guarded and checks violation event | - |
| policy loader | Y | test_policy_loader.py: load_pack swebench_safe_v1 (required keys, name, version, allowed_tools, denied, budgets, allowed_binaries), policy_hash deterministic, unknown pack raises ValueError, missing file raises FileNotFoundError | - |
| cost_report.py | Y | test_cost_report.py: build_cost_report shape, write_cost_report/write_summary and load_summary/load_cost_report roundtrip | - |
| proof_hook.py | Y | test_proof_hook.py: run_proof success writes proof.ok and proof_artifact_hash.txt; lake not found returns failure and no proof.ok | - |
| validate_pf_run.py | Y | test_validate_pf_run.py: compliance present vs missing | - |
| util.py (sanitize_instance_id) | Y (indirect) | Used in runner and tests | - |
| constants.py | Y (indirect) | Imported by runner, run_evidence | - |
| compare_runs.py | Y | test_experiments_compare_runs.py: aggregate, gates, schema validation | - |
| validate_predictions.py | Y | test_validate_predictions.py: good/empty/pfmeta/diff, run_status/allow-partial | - |
| check_wsl_env.py | Y | test_check_wsl_env.py: fails with clear message when resource/fcntl missing (non-WSL), Docker unavailable or not found, datasets/swebench missing, openhands missing; passes when all mocked ok | - |
| check_no_stub.py | Y | test_check_no_stub.py: stub present vs clean | - |
| fill_manifest_from_run.py | Y | test_fill_manifest_from_run.py: writes pf_commit and created_at; copies OPENHANDS_COMMIT/AGENT_COMMIT to agent_commit; writes experiment_manifest.json to run_dir when passed; not-in-git returns empty pf_commit, still writes created_at | - |
| list_delta_cases.py | Y | test_list_delta_cases.py: given synthetic compare.csv, produces baseline_solved_pf_failed.txt, pf_solved_baseline_failed.txt, both_solved.txt, pf_violations_on_solved.txt with expected instance IDs | - |
| bucket_pf_failures_from_cases.py | Y | test_bucket_pf_failures.py: given synthetic compare.csv and case bundles, produces CSV with instance_id, bucket, pf_status, baseline_status, violations, reason_codes, notes | - |
| Other experiments scripts (extract_case_bundle, etc.) | N | - | extract_case_bundle, run_swebench_eval, export_publish_artifacts: used in COMMANDS; no dedicated unit tests. Risk: CLI contract drift. |
| policy guard (deny/allow) | Y | test_policy_guard_deny_allow.py: deny curl, wget, git clone https, pip install git+https; allow python -m pytest, pip install -e ., make test, grep, sed; allow writes under workspace; deny /tmp, /etc, -o to forbidden path | - |
| Fixtures instances_smoke.jsonl | Y (required) | tests skip if file missing (@pytest.mark.skipif not INSTANCES_SMOKE.exists()) | Fixture committed; gen_fake_runpair.py for synthetic tests. |

**CI (source of truth):** Run exactly what CI runs locally (same command line). From repo root:

```bash
pytest tests/test_experiments_compare_runs.py tests/test_validate_predictions.py tests/test_check_no_stub.py tests/test_validate_pf_run.py tests/test_loader_from_file.py tests/test_workspace_plan.py tests/test_replay_roundtrip.py tests/test_swebench_runner_smoke.py tests/test_openhands_engine.py tests/test_policy_loader.py tests/test_cost_report.py tests/test_proof_hook.py tests/test_check_wsl_env.py tests/test_fill_manifest_from_run.py tests/test_list_delta_cases.py tests/test_bucket_pf_failures.py tests/test_policy_guard_deny_allow.py -v
```

Workflow: .github/workflows/bench-swebench-unit.yaml (matrix: ubuntu-latest, windows-latest). The above pytest line is the single source of truth; the audit table matches these tests. .github/workflows/bench-swebench-smoke.yaml runs runner smoke.

---

## 3. Error handling and robustness

| Component | Failure mode | Observed behavior (code path) | User-visible outcome | Recommendation |
|-----------|--------------|-------------------------------|----------------------|----------------|
| Runner | instances-file missing | loader load_from_file: path.read_text() | OSError, "Error loading instances" (runner.py ~705), return 1 | Doc: require file to exist. |
| Runner | dataset load fails (HF network) | load_dataset raises; runner excepts at top level | "Error loading instances:", return 1 | - |
| Runner | workspace materialization fails mid-run | Per-instance try/except; _log "workspace: failed"; instance skipped or run without workspace for openhands | Partial run; some instances may have no workspace | Doc: run can be partial; run_status.json (partial/failed) and atomic predictions (.tmp, rename on success). |
| Runner | mid-run failure (any exception) | Predictions written to .tmp; on exception no rename; run_status.json written (same dir as predictions) with status partial/failed, instances_written | predictions.jsonl absent or partial; run_status.json present | validate_predictions checks run_status; use --allow-partial to validate partial runs. |
| Runner | OpenHands not installed | assert_openhands_available() before loop | Exit 1, clear message | Pass. |
| Runner | guard shell missing | guard_shell.exists(); openhands_extra_env set only if exists | Guard not used; run proceeds unguarded | Doc: guarded run requires guard script. |
| Runner | run_dir not writable | run_dir.mkdir(); inst_dir.mkdir() | OSError during run | - |
| Engine | git diff timeout | _get_patch_from_repo catches TimeoutExpired, returns fallback string | 81-byte patch; apply check fails; empty patch emitted | Documented. |
| Engine | trajectory missing or malformed JSONL | _parse_trajectory_for_trace returns empty trace; files_modified from _get_files_modified_from_repo | path-restricted uses repo --name-only | - |
| Workspace | clone failure | _run_git check=True | CalledProcessError; materialize_workspace raises | - |
| Workspace | reset/clean failure on reuse | try/except pass in workspace.py | Reuse continues; tree may stay dirty | Log warning. |
| compare_runs | baseline_run_dir missing | find_run_report, load_summary return None | solve_rate null; compare.json still written | Doc: run compare after harness. |
| validate_predictions | file empty or malformed JSONL | json.loads per line; errors appended | Exit 1, list of errors | Pass. |
| fill_manifest_from_run | not in git repo | git rev-parse HEAD in script | Likely CalledProcessError or empty pf_commit | Doc: run from repo root. |
| Boundary | max_instances=0 | runner: max_instances 0 vs None; loader treats None as no cap | Go CLI passes 0 as "no cap" (max_instances > 0 check) | CLI 0 = no cap; runner default None. Consistent. |
| Boundary | instance_ids_file empty | Allowed; id_set empty; loader returns all from dataset up to max_instances | Pass. |
| Boundary | instance_ids filter matches no rows | _collect returns []; instances = []; "No instances to run", return 1 | Pass. |

---

## 4. Schema and contracts

| Artifact | Schema (required keys) | Producer(s) | Consumer(s) | Validation |
|----------|-------------------------|-------------|-------------|------------|
| predictions.jsonl | instance_id, model_patch, model_name_or_path (SWE-bench) | runner.py write_evidence + emit_predictions_line | Harness, validate_predictions | validate_predictions: is_like_diff, count, instance_id set |
| predictions.pfmeta.jsonl | instance_id, run_id, ... (same order as predictions) | runner.py pfmeta_rows | - | validate_predictions: line count and instance_id alignment |
| compare.json | baseline.solve_rate, pf.solve_rate, delta, patch_apply, violation_reasons_top10, env_drift (optional) | compare_runs.aggregate() | Humans, list_delta_cases, extract scripts | experiments/schemas/compare_report.schema.json (optional jsonschema validation in compare_runs) |
| compare.csv | Per-instance rows + _summary | compare_runs write_csv | extract_baseline_solved_pf_failed, list_delta_cases | None |
| runs/<run_id>/<instance_id>/ | metadata.json, run.log, model.patch, patch_apply_check.json, workspace_manifest.json, evidence/, cost_report.json, etc. | runner write_evidence; constants.*_FILENAME | run_evidence.load_*, compare_runs | - |
| manifest.json | experiment_id, pf_commit, budgets, model, dataset, policy_pack, seed, run_modes, ... | fill_manifest_from_run, hand | compare_runs --experiment-dir, COMMANDS | None |
| Harness run report | resolved_ids or resolved_instances, total_instances, ... | swebench harness | harness_report.find_run_report, load_run_report; compare_runs | None |

Run dir layout (constants): PATCH_APPLY_CHECK_FILENAME, COMPLIANCE_FILENAME, COST_REPORT_FILENAME, SUMMARY_JSON_FILENAME, REPLAY_BUNDLE_FILENAME, PROOF_OK_FILENAME. run_evidence.py and compare_runs import from constants.

---

## 5. Security and credentials

| Touch point | Safe (Y/N) | Evidence |
|-------------|------------|----------|
| API keys | Y | env-checklist and .env (gitignored); no keys in runner or engine code; run.log and stderr do not log env. |
| Path injection | Y | sanitize_instance_id used for run_dir and workspace paths (runner, run_evidence); instance_id from dataset or file, not raw user argv for subprocess cwd. |
| Guard executor | Y | pf_guard_exec.sh/bat receive PF_* env and workspace path; no privilege escalation in executor.py. |
| compare.json / run logs | Y | No credential fields written. |

---

## 6. Reproducibility and drift

| Item | Status | Note |
|------|--------|------|
| Seed | Documented | manifest seed=42; runner --seed; OPENHANDS_SEED in runner (args.seed). sample_lite_instance_ids --seed 42. |
| Manifest pf_commit, agent_commit | fill_manifest_from_run | Sets from git rev-parse HEAD; OPENHANDS_COMMIT/AGENT_COMMIT env. When not in git: script may fail or leave empty. |
| instance_ids.txt | Stable list | COMMANDS: do not change during iteration; sample_lite_instance_ids regenerates with --seed 42 and round-robin. |
| RUN_IDS policy | Documented + script | run-ids.md: canonical update via update_run_ids_if_green.py (only when all gates pass). |
| Drift risks | env.json + env_drift | Runner writes runs/<run_id>/env.json (python_version, platform, dataset, split, pip_freeze_hash); compare_runs adds env_drift to compare.json when baseline vs PF env differs. |

---

## 7. Technical debt and duplication

| Pattern | Location | Recommendation |
|---------|----------|----------------|
| Two entry points | pf bench swebench run (main.go builds pyArgs) vs python bench/swebench/runner.py | Document both; CLI passes --openhands-max-iterations when > 0; run-baseline-pf-cycle.sh falls back to Python runner when pf not on PATH. |
| run_evidence vs compare_runs | run_evidence loads summary, cost, compliance, patch_apply_check; compare_runs uses run_evidence and harness_report | Shared constants; no duplicate load logic. |
| Magic numbers | openhands_engine: _STAT_TIMEOUT, _PATH_DIFF_TIMEOUT, _DIFF_STAT_FILE_THRESHOLD, _PATH_RESTRICTED_MAX_PATHS_FALLBACK, _NAME_ONLY_QUICK_TIMEOUT; constants: MAX_PATCH_BYTES, GIT_DIFF_TIMEOUT | In engine or constants; README documents user-facing ones (PF_*). |
| Import paths | runner: from loader import, from workspace import (relative to bench/swebench when run as script); experiments: sys.path.insert(REPO_ROOT), from experiments.*, bench.swebench.* | COMMANDS "Without pf CLI" uses cd bench/swebench so imports resolve. |

---

## 8. Experiments workflow and scripts (correctness)

| Script | Produces | Consumes | Requires WSL | Requires Docker | Requires run_id |
|--------|----------|----------|-------------|-----------------|------------------|
| wsl-baseline-pf-cycle.sh | baseline/pf predictions, run dirs, compare | .env, instance_ids.txt, manifest | Y | Y (harness) | N (prints RUN_ID) |
| run-baseline-pf-cycle.sh | Same (uses pf CLI) | pf CLI, env | Y | Y | N |
| compare_runs.py | compare.json, compare.csv | baseline/eval, pf/eval, baseline_run_dir, pf_run_dir, experiment_dir | N | N | Y (run dir paths) |
| validate_predictions.py | Exit 0/1 | predictions.jsonl, instance_ids_file | N | N | N |
| check_no_stub.py | Exit 0/1 | run root dirs (baseline, pf) | N | N | N |
| check_wsl_env.py | Exit 0/1 | - | N (run on WSL to verify) | N | N |
| fill_manifest_from_run.py | Updated manifest.json | manifest path, git, optional run_dir | N | N | N |
| run_swebench_eval.py | eval dir (harness output) | predictions.jsonl, run dir, Docker | Y | Y | N |
| collect_eval_results.py | Summary from eval dirs | baseline/eval, pf/eval | N | N | N |
| list_delta_cases, extract_*, bucket_*, categorize_* | Debug artifacts | compare.csv, run dirs | N | N | Y (paths) |

Order of operations (COMMANDS Case 1): 1.1 baseline run, 1.2 PF run, validate_predictions, check_no_stub, 1.3 harness (run_swebench_eval), 1.4 compare (compare_runs with run IDs). Correct.

Harness: run_swebench_eval.py invokes swebench harness; collect_eval_results expects eval dirs with run report JSON (resolved_ids or resolved_instances). harness_report.find_run_report discovers it.

---

## 9. Edge cases and "lie detection"

| Claim or edge | Finding | Recommendation |
|---------------|---------|----------------|
| Empty predictions | Runner emits empty model_patch when cap or apply check fails. Docs: "empty patch so harness counts as failed." validate_predictions has --allow-empty-patch (e.g. when OpenHands not installed). | When comparing baseline vs PF, do not use --allow-empty-patch; empty is intentional for cap/timeout/apply fail. |
| Stub | check_no_stub.py fails if .swebench_stub in any model.patch. Runner and mock_engine do not write .swebench_stub (mock writes .pf_mock_smoke diff). | Pass. |
| "First valid baseline + PF pair" | run-baseline-pf-cycle.sh and wsl-baseline-pf-cycle.sh: "valid" means run completes; run-ids.md updated only via update_run_ids_if_green.py when all gates pass. | Doc: run-ids.md and commands.md describe update_run_ids_if_green.py. |
| Preflight | README: preflight does not run OpenHands; only materialize + git stat. "Preflight does not guarantee a successful full run (e.g. large repo can still timeout during agent run)." | Pass. |

---

## Appendix

### Full file list in scope (PF-owned only; excludes workspaces/*/repo cloned content)

**bench/swebench:** runner.py, loader.py, workspace.py, constants.py, util.py, cost_report.py, proof_hook.py, validate_pf_run.py, run_replay.py; engines/__init__.py, engines/openhands_engine.py, engines/mock_engine.py; replay/__init__.py, replay/replay.py, replay/capture.py, replay/__main__.py, replay/README.md; guard/pf_guard_exec.sh, guard/pf_guard_exec.bat, guard/executor.py; policy/__init__.py, policy/loader.py, policy/packs/swebench_safe_v1.yaml; fixtures/instances_smoke.jsonl, fixtures/instance_corrupted_patch.jsonl, fixtures/README.md; schemas/pf_run_metadata.json; README.md.

**experiments:** README.md, __init__.py, run_evidence.py, harness_report.py; scripts/compare_runs.py, validate_predictions.py, run_swebench_eval.py, collect_eval_results.py, check_wsl_env.py, check_no_stub.py, fill_manifest_from_run.py, list_delta_cases.py, extract_case_bundle.py, extract_baseline_solved_pf_failed.py, bucket_pf_failures_from_cases.py, categorize_pf_failures.py, sample_lite_instance_ids.py, export_publish_artifacts.py, update_run_ids_if_green.py, run-baseline-pf-cycle.sh; exp-step2-lite-smoke/manifest.json, instance_ids.txt, env-checklist.md, commands.md, run-ids.md; exp-step2-lite-stress-large-repos/ (manifest.json, instance_ids.txt, README.md); schemas/compare_report.schema.json (includes empty_patch_reasons_topN, reproducibility fields).

**Integration:** core/cli/pf/main.go (swebenchRunCmd, swebenchReplayCmd); .github/workflows/bench-swebench-smoke.yaml.

**Docs:** [pf-solve-rate-debugging.md](pf-solve-rate-debugging.md).

### Test commands run (evidence)

- **Smoke:** `pytest tests/test_swebench_runner_smoke.py -q --tb=short` (CI and local).
- **Unit suite (bench-swebench-unit):** `pytest tests/test_experiments_compare_runs.py tests/test_validate_predictions.py tests/test_check_no_stub.py tests/test_validate_pf_run.py tests/test_loader_from_file.py tests/test_workspace_plan.py tests/test_replay_roundtrip.py tests/test_swebench_runner_smoke.py tests/test_openhands_engine.py tests/test_policy_loader.py tests/test_cost_report.py tests/test_proof_hook.py -v` (CI `.github/workflows/bench-swebench-unit.yaml` on ubuntu-latest and windows-latest). Covers compare aggregate (solve rates, patch_apply, empty_patch_reasons_topN, reproducibility), run_id consistency when --require-harness, gates, schema; validate_predictions; check_no_stub; validate_pf_run; loader; workspace plan; replay (skipped on Windows); openhands_engine (timeout fallback skipped on Windows); policy loader; cost_report; proof_hook.

### Manual run evidence

To remove "Manual run evidence: none" and produce a golden Step-2 parity cycle:

**3.0.A — WSL prerequisites (one-time).** From repo root in WSL run and confirm exit 0 for each:

- `pf --help`
- `python -c "import openhands, datasets, swebench; print('deps ok')"`
- `docker info >/dev/null`
- `python experiments/scripts/check_wsl_env.py`

**3.0.B — Full pipeline.** Run `bash experiments/scripts/run-baseline-pf-cycle.sh` (or the explicit Case 1.1 to 1.2 to validations to harness to compare in commands.md). Acceptance gates: validate_predictions on baseline and PF without --allow-partial; check_no_stub passes; validate_pf_run passes for PF run dir; harness reports under baseline/eval and pf/eval; compare_runs.py --require-harness --require-compliance --require-patch-apply exits 0; compare.json has numeric solve rates and patch_apply.applies_false == 0.

**3.0.C — Update RUN_IDS.** Run `python experiments/scripts/update_run_ids_if_green.py --experiment-dir runs/exp-step2-lite-smoke --baseline-run-dir runs/exp-step2-lite-smoke/baseline/<BASELINE_RUN_ID> --pf-run-dir runs/exp-step2-lite-smoke/pf/<PF_RUN_ID>`. Acceptance: run-ids.md is updated and script logs that all gates passed.

**3.0.D — Publish and delta bundles.** Run export_publish_artifacts.py then list_delta_cases.py and extract_case_bundle.py (see commands.md). If there are no deltas, baseline_solved_pf_failed.txt is empty and extract_case_bundle no-ops with a short message.

**Evidence to record after a run:** (1) Date and WSL environment where 3.0.A and 3.0.B were run. (2) Commit or path where run-ids.md was updated. (3) Confirmation that compare.json had numeric solve rates and patch_apply.applies_false == 0. Fill in below when available:

- **Last golden run (WSL):** _Date and RUN_IDS run IDs to be filled after first successful full cycle._
- **Gates passed:** _validate_predictions (both), check_no_stub, validate_pf_run, harness reports present, compare with --require-harness --require-compliance --require-patch-apply, patch_apply.applies_false == 0._
