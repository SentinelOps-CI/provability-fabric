#!/usr/bin/env bash
# Full Step-2 parity cycle in WSL: env + credentials, preflight, baseline run, PF run,
# validations, harness, gated compare, run-ids reminder, delta triage.
# This script is wired for OpenHands. For the default direct_agent engine, use:
#   bash experiments/scripts/run-baseline-pf-cycle.sh
# Run from repo root: bash experiments/scripts/wsl-baseline-pf-cycle.sh [MAX_INSTANCES]
# Example: bash experiments/scripts/wsl-baseline-pf-cycle.sh 2   (only 2 instances, for testing)
set -e

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

MAX_INSTANCES="${1:-20}"

# Load API keys (repo root .env is gitignored)
if [ -f .env ]; then
  set -a
  source .env
  set +a
  echo "Loaded .env (OPENAI_API_KEY, ANTHROPIC_API_KEY, OPENHANDS_API_KEY, OPENAI_BASE_URL)"
else
  echo "Warning: .env not found. Export OPENAI_API_KEY (and optionally ANTHROPIC_API_KEY, OPENHANDS_API_KEY) before running."
fi

export OPENAI_BASE_URL="${OPENAI_BASE_URL:-}"

echo ""
echo "=== Manifest fill (model.id for resolve) ==="
python experiments/scripts/fill_manifest_from_run.py experiments/exp-step2-lite-smoke/manifest.json

echo ""
echo "=== Preflight (must be green) ==="
python experiments/scripts/check_wsl_env.py --strict-linux

EFFECTIVE_MODEL="$(python experiments/scripts/resolve_cycle_llm.py experiments/exp-step2-lite-smoke/manifest.json)" || exit 1
export OPENHANDS_MODEL="$EFFECTIVE_MODEL"
echo "[cycle] model=$EFFECTIVE_MODEL provider=${OPENHANDS_PROVIDER:-openai}"
python experiments/scripts/ensure_openhands_config.py || exit 1

echo ""
echo "=== Baseline run (real OpenHands, unguarded) — $MAX_INSTANCES instances ==="
mkdir -p runs/exp-step2-lite-smoke/baseline
cd bench/swebench
python runner.py \
  --dataset lite \
  --instance-ids-file ../../experiments/exp-step2-lite-smoke/instance_ids.txt \
  --max_instances "$MAX_INSTANCES" \
  --experiment-dir ../../experiments/exp-step2-lite-smoke \
  --engine openhands \
  --openhands-model "$EFFECTIVE_MODEL" \
  --seed 42 \
  --out ../../runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --runs-dir ../../runs/exp-step2-lite-smoke/baseline
cd "$REPO_ROOT"

BASELINE_RUN_ID="$(ls -1dt runs/exp-step2-lite-smoke/baseline/20* 2>/dev/null | head -1 | xargs basename)"
echo "BASELINE_RUN_ID=$BASELINE_RUN_ID"

echo ""
echo "=== Validate baseline predictions ==="
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  -n "$MAX_INSTANCES" \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --allow-empty-patch

echo ""
echo "=== PF-guarded run (policy + evidence) — $MAX_INSTANCES instances ==="
mkdir -p runs/exp-step2-lite-smoke/pf
cd bench/swebench
python runner.py \
  --dataset lite \
  --instance-ids-file ../../experiments/exp-step2-lite-smoke/instance_ids.txt \
  --max_instances "$MAX_INSTANCES" \
  --experiment-dir ../../experiments/exp-step2-lite-smoke \
  --engine openhands \
  --openhands-model "$EFFECTIVE_MODEL" \
  --mode pf_guarded \
  --seed 42 \
  --policy swebench_safe_v1 \
  --out ../../runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --runs-dir ../../runs/exp-step2-lite-smoke/pf
cd "$REPO_ROOT"

PF_RUN_ID="$(ls -1dt runs/exp-step2-lite-smoke/pf/20* 2>/dev/null | head -1 | xargs basename)"
echo "PF_RUN_ID=$PF_RUN_ID"

echo ""
echo "=== Step-2 hard validity gates ==="
python experiments/scripts/validate_predictions.py \
  runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  -n "$MAX_INSTANCES" \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --allow-empty-patch

python experiments/scripts/check_no_stub.py \
  runs/exp-step2-lite-smoke/baseline \
  runs/exp-step2-lite-smoke/pf

python bench/swebench/validate_pf_run.py "runs/exp-step2-lite-smoke/pf/$PF_RUN_ID"

echo ""
echo "=== Harness eval (baseline) ==="
python -m swebench.harness.run_evaluation \
  --predictions_path runs/exp-step2-lite-smoke/baseline/predictions.jsonl \
  --dataset_name SWE-bench/SWE-bench_Lite \
  --split test \
  --run_id baseline \
  --report_dir runs/exp-step2-lite-smoke/baseline/eval

echo ""
echo "=== Harness eval (PF) ==="
python -m swebench.harness.run_evaluation \
  --predictions_path runs/exp-step2-lite-smoke/pf/predictions.jsonl \
  --dataset_name SWE-bench/SWE-bench_Lite \
  --split test \
  --run_id pf \
  --report_dir runs/exp-step2-lite-smoke/pf/eval

echo ""
echo "=== Compare with hard gates (Step-2 complete check) ==="
python experiments/scripts/compare_runs.py \
  --experiment-dir runs/exp-step2-lite-smoke \
  --baseline-run-dir "runs/exp-step2-lite-smoke/baseline/$BASELINE_RUN_ID" \
  --pf-run-dir "runs/exp-step2-lite-smoke/pf/$PF_RUN_ID" \
  --require-harness \
  --require-compliance \
  --require-patch-apply \
  --require-priced-models

echo ""
echo "=== Update run-ids.md (manual) ==="
echo "Prefer the green gate (same validation as run-baseline-pf-cycle.sh --update-run-ids):"
echo "  python experiments/scripts/update_run_ids_if_green.py \\"
echo "    --experiment-dir experiments/exp-step2-lite-smoke \\"
echo "    --baseline-run-dir runs/exp-step2-lite-smoke/baseline/$BASELINE_RUN_ID \\"
echo "    --pf-run-dir runs/exp-step2-lite-smoke/pf/$PF_RUN_ID \\"
echo "    --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \\"
echo "    --allow-empty-patch"
echo "Or edit experiments/exp-step2-lite-smoke/run-ids.md and set:"
echo "  Baseline (Case 1.1): $BASELINE_RUN_ID"
echo "  PF-guarded (Case 1.2): $PF_RUN_ID"

echo ""
echo "=== Delta triage ==="
mkdir -p runs/exp-step2-lite-smoke/analysis
python experiments/scripts/list_delta_cases.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --out-dir runs/exp-step2-lite-smoke/analysis

python experiments/scripts/extract_case_bundle.py \
  --instance-ids-file runs/exp-step2-lite-smoke/analysis/baseline_solved_pf_failed.txt \
  --baseline-run-dir "runs/exp-step2-lite-smoke/baseline/$BASELINE_RUN_ID" \
  --pf-run-dir "runs/exp-step2-lite-smoke/pf/$PF_RUN_ID" \
  --baseline-eval-dir runs/exp-step2-lite-smoke/baseline/eval \
  --pf-eval-dir runs/exp-step2-lite-smoke/pf/eval \
  --out-dir runs/exp-step2-lite-smoke/analysis/cases

python experiments/scripts/bucket_pf_failures_from_cases.py \
  --compare-csv runs/exp-step2-lite-smoke/compare.csv \
  --cases-dir runs/exp-step2-lite-smoke/analysis/cases \
  --out-csv runs/exp-step2-lite-smoke/analysis/pf_failure_buckets.csv

echo ""
echo "Done. run-ids.md update is manual; then you are green for Step 2."
echo "To run with fewer instances (e.g. 2): bash experiments/scripts/wsl-baseline-pf-cycle.sh 2"
