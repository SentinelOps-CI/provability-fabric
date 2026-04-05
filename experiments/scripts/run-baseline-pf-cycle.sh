#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Run the first fully-valid baseline + PF-guarded pair (plan: first_valid_baseline_pf_pair).
# Canonical Step-2 entrypoint: env check, baseline, PF, validations, harness, compare with gates.
# Execute from repository root inside WSL or Linux. Do not run on Windows-native (harness requires Unix).
# Default agent engine: direct_agent (native OpenAI-compatible loop). Override: --engine openhands or PF_CYCLE_ENGINE=openhands.
# Model: OPENHANDS_MODEL overrides manifest model.id; both required to resolve (manifest after Phase 1.2).
# Provider: OPENHANDS_PROVIDER=openai|anthropic|prime_intellect (default openai). See env-checklist.md.
# Options: --engine NAME   openhands | direct_agent | mock (default direct_agent)
#          --update-run-ids  after compare passes, update run-ids.md via update_run_ids_if_green.py
#          --triage         after compare, run list_delta_cases + extract_case_bundle (and optionally export_publish_artifacts)
#
# If bash reports $'\r': command not found, a script or .env has Windows CRLF; fix with:
#   sed -i 's/\r$//' .env
# Smoke run (optional): To validate one instance before a full baseline/PF run, invoke the runner with
#   --max_instances 1  (and the same --out / --runs-dir). Phase 1.1 and the pre-Phase 4.1 harness deps
#   check (requests, datasets) catch env and harness issues early.
set -e

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

# Preflight: small GCP/VM root disks often hit ENOSPC; git then leaves index.lock and pull fails.
if [ -f "$REPO_ROOT/.git/index.lock" ]; then
  echo "Warning: removing stale $REPO_ROOT/.git/index.lock (safe if no other git process is running)." >&2
  rm -f "$REPO_ROOT/.git/index.lock"
fi
avail_kb=$(df -k "$REPO_ROOT" 2>/dev/null | awk 'NR==2 {print $4}') || avail_kb=""
if [ -n "$avail_kb" ] && [ "$avail_kb" -lt 524288 ] 2>/dev/null; then
  echo "Warning: less than 512 MiB free on the repo filesystem. git pull/Docker may fail; run: docker system prune -af, sudo journalctl --vacuum-size=100M, or grow the disk." >&2
  df -h "$REPO_ROOT" 2>/dev/null | head -5 >&2 || true
fi

# Load .env if present (OPENAI_API_KEY, ANTHROPIC_API_KEY, PRIME_INTELLECT_API_KEY, etc.) for the LLM.
# Strip CRLF (Windows line endings) so keys are not invalidated by trailing \r.
if [ -f "$REPO_ROOT/.env" ]; then
  set -a
  # Strip CRLF so API keys from Windows-edited .env are valid
  # shellcheck source=/dev/null
  . <(tr -d '\r' < "$REPO_ROOT/.env")
  set +a
fi
# Subprocesses (pf, python) only see exported variables; default avoids silent openai routing.
export OPENHANDS_PROVIDER="${OPENHANDS_PROVIDER:-openai}"

# Prefer repo venv (WSL often has externally-managed system Python; venv avoids pip errors)
if [ -x "$REPO_ROOT/.venv-wsl/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv-wsl/bin/python"
elif [ -x "$REPO_ROOT/.venv/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv/bin/python"
elif command -v python3 >/dev/null 2>&1; then
  PYTHON=python3
elif command -v python >/dev/null 2>&1; then
  PYTHON=python
else
  echo "Error: python or python3 not found. Install Python 3 and ensure it is on PATH."
  exit 1
fi

# Ensure venv bin is on PATH so the OpenHands engine's subprocess finds the openhands CLI
if [ -n "$PYTHON" ] && [ -x "$PYTHON" ]; then
  VENV_BIN="$(dirname "$PYTHON")"
  if [ -x "$VENV_BIN/openhands" ]; then
    export PATH="$VENV_BIN:$PATH"
  fi
fi

ENGINE="${PF_CYCLE_ENGINE:-direct_agent}"
UPDATE_RUN_IDS=
TRIAGE=
while [ $# -gt 0 ]; do
  case "$1" in
    --update-run-ids) UPDATE_RUN_IDS=1; shift ;;
    --triage) TRIAGE=1; shift ;;
    --engine)
      if [ $# -lt 2 ]; then echo "Error: --engine requires a value (openhands|direct_agent|mock)" >&2; exit 1; fi
      ENGINE="$2"
      shift 2 ;;
    *)
      echo "Error: unknown option: $1" >&2
      echo "Usage: $0 [--engine openhands|direct_agent|mock] [--update-run-ids] [--triage]" >&2
      exit 1 ;;
  esac
done
case "$ENGINE" in
  openhands|direct_agent|mock) ;;
  *)
    echo "Error: --engine must be openhands, direct_agent, or mock (got: $ENGINE)" >&2
    exit 1 ;;
esac

# direct_agent + default fallback hides failures behind OpenHands CLI and used a tiny task budget (see PF_OPENHANDS_MAX_TASK_CHARS).
# For this canonical cycle, stay on direct_agent unless you explicitly export PF_DIRECT_AGENT_FALLBACK_OPENHANDS=1.
if [ "$ENGINE" = "direct_agent" ]; then
  export PF_DIRECT_AGENT_FALLBACK_OPENHANDS="${PF_DIRECT_AGENT_FALLBACK_OPENHANDS:-0}"
  echo "[cycle] PF_DIRECT_AGENT_FALLBACK_OPENHANDS=$PF_DIRECT_AGENT_FALLBACK_OPENHANDS (set to 1 to retry failures via OpenHands subprocess)"
fi

EXP=runs/exp-step2-lite-smoke
BASELINE_DIR=$EXP/baseline
PF_DIR=$EXP/pf
ANALYSIS=$EXP/analysis
MANIFEST_JSON=experiments/exp-step2-lite-smoke/manifest.json

case "$(uname -s 2>/dev/null)" in
  Linux) ;;
  *)
    echo "Error: run-baseline-pf-cycle.sh must run under WSL or Linux (uname -s must be Linux). Re-open repo in WSL, activate .venv-wsl, re-run."
    exit 1
    ;;
esac

echo "=== Phase 1.1: WSL environment hard check (engine=$ENGINE) ==="
if [ "$ENGINE" = "direct_agent" ] || [ "$ENGINE" = "mock" ]; then
  $PYTHON experiments/scripts/check_wsl_env.py --strict-linux --skip-openhands
else
  $PYTHON experiments/scripts/check_wsl_env.py --strict-linux
fi
docker info >/dev/null 2>&1 || { echo "docker info failed"; exit 1; }
$PYTHON -c "import resource, fcntl; print('unix modules ok')"
$PYTHON -c "import datasets, swebench; print('datasets+swebench ok')"
if [ "$ENGINE" = "openhands" ]; then
  $PYTHON -c "import openhands; print('openhands ok')"
fi
echo "Phase 1.1 passed."

echo ""
echo "=== Phase 1.2: Fill/pin experiment manifest ==="
$PYTHON experiments/scripts/fill_manifest_from_run.py "$MANIFEST_JSON"
echo "Phase 1.2 done."

echo ""
echo "=== Phase 1.3: Resolve LLM model and provider ==="
EFFECTIVE_MODEL="$($PYTHON experiments/scripts/resolve_cycle_llm.py "$MANIFEST_JSON")" || exit 1
export OPENHANDS_MODEL="$EFFECTIVE_MODEL"
echo "[cycle] OPENHANDS_PROVIDER=${OPENHANDS_PROVIDER:-openai}"
echo "[cycle] Effective model (OPENHANDS_MODEL): $EFFECTIVE_MODEL"
echo "[cycle] SWE-bench engine: $ENGINE"

echo ""
echo "=== Phase 2.1: Baseline run (unguarded, engine=$ENGINE) ==="
PROVIDER="${OPENHANDS_PROVIDER:-openai}"
if [ "$ENGINE" != "mock" ]; then
  case "$PROVIDER" in
    openai)
      $PYTHON -c "import os; key=os.environ.get('OPENAI_API_KEY',''); print('[env] OPENAI_API_KEY: %s (len=%d)' % ('set' if key else 'NOT SET', len(key.strip())))"
      if [ -z "${OPENAI_API_KEY:-}" ]; then
        echo "Error: OPENAI_API_KEY is required for OPENHANDS_PROVIDER=openai."
        exit 1
      fi
      $PYTHON experiments/scripts/check_openai_key.py || { echo "OpenAI API key check failed."; exit 1; }
      ;;
    anthropic)
      if [ -z "${ANTHROPIC_API_KEY:-}" ]; then
        echo "Error: ANTHROPIC_API_KEY required for OPENHANDS_PROVIDER=anthropic."
        exit 1
      fi
      ;;
    prime_intellect)
      $PYTHON -c "import os; print('[env] PRIME_INTELLECT_API_KEY:', 'set' if os.environ.get('PRIME_INTELLECT_API_KEY','').strip() else 'NOT SET')"
      if [ -z "${PRIME_INTELLECT_API_KEY:-}" ]; then
        echo "Error: PRIME_INTELLECT_API_KEY required for OPENHANDS_PROVIDER=prime_intellect."
        exit 1
      fi
      ;;
  esac
else
  echo "[cycle] mock engine: skipping LLM API key checks"
fi
if [ "$ENGINE" = "openhands" ]; then
  $PYTHON experiments/scripts/ensure_openhands_config.py || { echo "OpenHands headless config check failed. Fix the error above and re-run."; exit 1; }
fi
if command -v pf >/dev/null 2>&1; then
  RUN_CMD="pf bench swebench run"
else
  RUN_CMD="$PYTHON bench/swebench/runner.py"
fi
mkdir -p "$BASELINE_DIR"
BASELINE_LOG=$(mktemp)
# OPENHANDS_TIMEOUT env overrides per-instance timeout (default 1200s; align with manifest budgets.timeout_sec)
OPENHANDS_TIMEOUT=${OPENHANDS_TIMEOUT:-1200}
# Prime local compat proxy upstream read (default was 180s → "Remote end closed connection" on slow turns).
export PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S="${PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S:-$OPENHANDS_TIMEOUT}"
$RUN_CMD \
  --dataset Lite \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine "$ENGINE" \
  --openhands-model "$EFFECTIVE_MODEL" \
  --openhands-timeout "$OPENHANDS_TIMEOUT" \
  --seed 42 \
  --out "$BASELINE_DIR/predictions.jsonl" \
  --runs-dir "$BASELINE_DIR" 2>&1 | tee "$BASELINE_LOG"
BASELINE_RUN_ID=$(grep -o 'Run ID: [^[:space:]]*' "$BASELINE_LOG" | tail -1 | sed 's/Run ID: //')
rm -f "$BASELINE_LOG"
if [ -z "$BASELINE_RUN_ID" ]; then
  echo "Error: Could not capture baseline Run ID. Check baseline run output."
  exit 1
fi
echo "Baseline Run ID: $BASELINE_RUN_ID"

echo ""
echo "=== Phase 2.2: Post-baseline validation ==="
$PYTHON experiments/scripts/validate_predictions.py \
  "$BASELINE_DIR/predictions.jsonl" \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --allow-empty-patch
$PYTHON experiments/scripts/check_no_stub.py "$BASELINE_DIR"
echo "Phase 2.2 passed."

echo ""
echo "=== Phase 3.1: PF-guarded run (engine=$ENGINE) ==="
mkdir -p "$PF_DIR"
PF_LOG=$(mktemp)
$RUN_CMD \
  --dataset Lite \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine "$ENGINE" \
  --openhands-model "$EFFECTIVE_MODEL" \
  --openhands-timeout "$OPENHANDS_TIMEOUT" \
  --mode pf_guarded \
  --seed 42 \
  --policy swebench_safe_v1 \
  --out "$PF_DIR/predictions.jsonl" \
  --runs-dir "$PF_DIR" 2>&1 | tee "$PF_LOG"
PF_RUN_ID=$(grep -o 'Run ID: [^[:space:]]*' "$PF_LOG" | tail -1 | sed 's/Run ID: //')
rm -f "$PF_LOG"
if [ -z "$PF_RUN_ID" ]; then
  echo "Error: Could not capture PF Run ID. Check PF run output."
  exit 1
fi
echo "PF Run ID: $PF_RUN_ID"

echo ""
echo "=== Phase 3.2: Post-PF validation ==="
$PYTHON experiments/scripts/validate_predictions.py \
  "$PF_DIR/predictions.jsonl" \
  -n 20 \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --allow-empty-patch
$PYTHON bench/swebench/validate_pf_run.py "$PF_DIR/$PF_RUN_ID"
$PYTHON experiments/scripts/check_no_stub.py "$BASELINE_DIR" "$PF_DIR"
echo "Phase 3.2 passed."

echo ""
echo "=== Phase 4.1: SWE-bench harness ==="
# Fail fast if harness deps (requests, datasets) are broken; Phase 1.1 already imports them.
$PYTHON -c "import requests; import datasets; print('harness deps ok')" || { echo "Harness deps failed (e.g. IndentationError in requests). Fix: pip install --force-reinstall requests"; exit 1; }
$PYTHON experiments/scripts/run_swebench_eval.py \
  --baseline-predictions "$BASELINE_DIR/predictions.jsonl" \
  --pf-predictions "$PF_DIR/predictions.jsonl" \
  --baseline-eval-dir "$BASELINE_DIR/eval" \
  --pf-eval-dir "$PF_DIR/eval" \
  --rm-stale-eval-containers
echo "Phase 4.1 done."

echo ""
echo "=== Phase 4.2: Replay sample (PF-resolved, zero violations) ==="
$PYTHON experiments/scripts/run_replay_sample.py \
  --pf-eval-dir "$PF_DIR/eval" \
  --pf-run-dir "$PF_DIR/$PF_RUN_ID" \
  --runs-dir "$PF_DIR" \
  --max-sample 5 \
  --out "$EXP/replay_summary.json" || true
echo "Phase 4.2 done."

echo ""
echo "=== Phase 4.3: Compare with hard gates ==="
$PYTHON experiments/scripts/compare_runs.py \
  --experiment-dir "$EXP" \
  --baseline-run-dir "$BASELINE_DIR/$BASELINE_RUN_ID" \
  --pf-run-dir "$PF_DIR/$PF_RUN_ID" \
  --require-harness \
  --require-compliance \
  --require-patch-apply \
  --require-priced-models
echo "Phase 4.3 passed."

echo ""
if [ -n "$UPDATE_RUN_IDS" ]; then
  echo "=== Phase 5a: Update run-ids.md (gates passed) ==="
  $PYTHON experiments/scripts/update_run_ids_if_green.py \
    --experiment-dir experiments/exp-step2-lite-smoke \
    --baseline-run-dir "$BASELINE_DIR/$BASELINE_RUN_ID" \
    --pf-run-dir "$PF_DIR/$PF_RUN_ID" \
    --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
    --allow-empty-patch
  echo "Phase 5a passed: run-ids.md updated."
else
  echo "=== Phase 5: Update run-ids.md (manual or use --update-run-ids) ==="
  echo "Update experiments/exp-step2-lite-smoke/run-ids.md with:"
  echo "  Baseline (Case 1.1): $BASELINE_RUN_ID"
  echo "  PF-guarded (Case 1.2): $PF_RUN_ID"
  echo "Or re-run with --update-run-ids to run update_run_ids_if_green.py automatically."
fi
echo "Optionally: $PYTHON experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json $BASELINE_DIR/$BASELINE_RUN_ID"
echo "Optionally: $PYTHON experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json $PF_DIR/$PF_RUN_ID"

echo ""
echo "=== Phase 6: Delta triage (list_delta_cases + extract_case_bundle) ==="
mkdir -p "$ANALYSIS"
$PYTHON experiments/scripts/list_delta_cases.py \
  --compare-csv "$EXP/compare.csv" \
  --out-dir "$ANALYSIS"
if [ -n "$TRIAGE" ]; then
  $PYTHON experiments/scripts/extract_case_bundle.py \
    --instance-ids-file "$ANALYSIS/baseline_solved_pf_failed.txt" \
    --baseline-run-dir "$BASELINE_DIR/$BASELINE_RUN_ID" \
    --pf-run-dir "$PF_DIR/$PF_RUN_ID" \
    --baseline-eval-dir "$BASELINE_DIR/eval" \
    --pf-eval-dir "$PF_DIR/eval" \
    --out-dir "$ANALYSIS/cases" || true
  $PYTHON experiments/scripts/bucket_pf_failures_from_cases.py \
    --compare-csv "$EXP/compare.csv" \
    --cases-dir "$ANALYSIS/cases" \
    --out-csv "$ANALYSIS/pf_failure_buckets.csv" 2>/dev/null || true
  echo "Phase 6 (--triage): case bundles and buckets written."
else
  echo "Run extract_case_bundle and bucket_pf_failures_from_cases manually, or re-run with --triage."
fi
echo "Fix order: patch_apply -> guard false positives -> budget/timeout -> agent recovery -> model quality."

echo ""
echo "=== Phase 7: Regression-slice rerun loop ==="
echo "After a fix: rerun only instances in $ANALYSIS/baseline_solved_pf_failed.txt (PF-guarded),"
echo "re-evaluate with harness, then compare new PF run to same baseline run ID ($BASELINE_RUN_ID)."
echo "Always use --require-harness --require-compliance --require-patch-apply on compare."
echo "See experiments/exp-step2-lite-smoke/commands.md 'Rerun only the regression slice'."
if [ "${PF_REQUIRE_NONZERO_SOLVE:-}" = 1 ]; then
  $PYTHON experiments/scripts/check_golden_solve_rates.py \
    --compare-json "$EXP/compare.json" \
    --require-nonzero || exit 1
fi
