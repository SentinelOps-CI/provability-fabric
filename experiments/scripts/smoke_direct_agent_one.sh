#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Single-instance direct_agent smoke (WSL/Linux): same model resolution as the Step-2 cycle,
# one Lite instance, non-guarded. Use after env check to confirm Prime/OpenAI path produces a patch.
#
# Usage (repo root):
#   bash experiments/scripts/smoke_direct_agent_one.sh
#   OPENHANDS_PROVIDER=prime_intellect bash experiments/scripts/smoke_direct_agent_one.sh
#
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

case "$(uname -s 2>/dev/null)" in
  Linux) ;;
  *)
    echo "Error: run under Linux or WSL (uname -s must be Linux)." >&2
    exit 1
    ;;
esac

if [ -f "$REPO_ROOT/.env" ]; then
  set -a
  # shellcheck source=/dev/null
  . <(tr -d '\r' < "$REPO_ROOT/.env")
  set +a
fi
export OPENHANDS_PROVIDER="${OPENHANDS_PROVIDER:-openai}"

if [ -x "$REPO_ROOT/.venv-wsl/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv-wsl/bin/python"
elif [ -x "$REPO_ROOT/.venv/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv/bin/python"
else
  PYTHON=python3
fi

MANIFEST_JSON="${SMOKE_MANIFEST:-experiments/exp-step2-lite-smoke/manifest.json}"
OPENHANDS_TIMEOUT="${OPENHANDS_TIMEOUT:-1200}"
export PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S="${PF_PRIME_PROXY_UPSTREAM_TIMEOUT_S:-$OPENHANDS_TIMEOUT}"

EFFECTIVE_MODEL="$($PYTHON experiments/scripts/resolve_cycle_llm.py "$MANIFEST_JSON")" || exit 1
export OPENHANDS_MODEL="$EFFECTIVE_MODEL"
echo "[smoke] OPENHANDS_PROVIDER=$OPENHANDS_PROVIDER OPENHANDS_MODEL=$OPENHANDS_MODEL"

if command -v pf >/dev/null 2>&1; then
  RUN_CMD="pf bench swebench run"
else
  RUN_CMD="$PYTHON bench/swebench/runner.py"
fi

OUT_DIR="${SMOKE_OUT_DIR:-runs/smoke-direct-agent-one}"
mkdir -p "$OUT_DIR"
rm -f "$OUT_DIR/predictions.jsonl" "$OUT_DIR/run_status.json"

$RUN_CMD \
  --dataset Lite \
  --split test \
  --instance-ids-file experiments/exp-step2-lite-smoke/instance_ids.txt \
  --max_instances 1 \
  --experiment-dir experiments/exp-step2-lite-smoke \
  --engine direct_agent \
  --openhands-model "$EFFECTIVE_MODEL" \
  --openhands-timeout "$OPENHANDS_TIMEOUT" \
  --seed 42 \
  --out "$OUT_DIR/predictions.jsonl" \
  --runs-dir "$OUT_DIR"

RUN_ID=""
STATUS_PATH="$OUT_DIR/run_status.json"
if [ -f "$STATUS_PATH" ]; then
  RUN_ID="$($PYTHON -c "import json,sys; print(json.load(open(sys.argv[1],encoding='utf-8')).get('run_id',''))" "$STATUS_PATH")"
fi
if [ -z "$RUN_ID" ]; then
  echo "Warning: could not read run_id from $OUT_DIR/run_status.json" >&2
  exit 1
fi

echo "[smoke] Run ID: $RUN_ID"
echo "[smoke] Health snapshot:"
$PYTHON experiments/scripts/run_health_snapshot.py --run-dir "$OUT_DIR/$RUN_ID" --sample 2

echo "[smoke] First prediction line (model_patch length):"
PRED_PATH="$OUT_DIR/predictions.jsonl"
$PYTHON -c "import json,sys; ln=open(sys.argv[1],encoding='utf-8').readline(); o=json.loads(ln); print('patch_len', len(o.get('model_patch') or ''))" "$PRED_PATH"
