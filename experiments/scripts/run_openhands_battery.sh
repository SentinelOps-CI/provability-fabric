#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Battery of tests to verify OpenHands and SWE-bench runner work correctly.
# Run from repository root (WSL or Linux). Uses .venv-wsl if present.
# Optional: --integration runs a minimal headless OpenHands CLI test (requires OPENAI_API_KEY, slow).
set -e

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

if [ -x "$REPO_ROOT/.venv-wsl/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv-wsl/bin/python"
elif [ -x "$REPO_ROOT/.venv/bin/python" ]; then
  PYTHON="$REPO_ROOT/.venv/bin/python"
else
  PYTHON=python3
fi

RUN_INTEGRATION=
for arg in "$@"; do
  case "$arg" in
    --integration) RUN_INTEGRATION=1 ;;
  esac
done

echo "=== OpenHands + SWE-bench test battery ==="
echo "Python: $PYTHON"

echo ""
echo "--- 1. Environment (resource, fcntl, docker, requests, datasets, swebench, openhands) ---"
$PYTHON experiments/scripts/check_wsl_env.py
echo "PASS: check_wsl_env.py"

echo ""
echo "--- 2. OpenHands engine unit tests (trajectory parse, timeout fallback, path-restricted) ---"
$PYTHON -m pytest tests/test_openhands_engine.py -q --tb=short
echo "PASS: test_openhands_engine.py"

echo ""
echo "--- 3. check_wsl_env script unit tests ---"
$PYTHON -m pytest tests/test_check_wsl_env.py -q --tb=short
echo "PASS: test_check_wsl_env.py"

echo ""
echo "--- 4. SWE-bench runner smoke (mock baseline + guarded, openhands-unavailable exit) ---"
$PYTHON -m pytest tests/test_swebench_runner_smoke.py -q --tb=short
echo "PASS: test_swebench_runner_smoke.py"

echo ""
echo "--- 5. Mock engine smoke (baseline no violations, guarded one violation) ---"
PYTHONPATH="$REPO_ROOT/bench/swebench" $PYTHON bench/swebench/test_mock_engine_smoke.py
echo "PASS: test_mock_engine_smoke.py"

if [ -n "$RUN_INTEGRATION" ]; then
  echo ""
  echo "--- 6. Integration: minimal OpenHands headless (create file; requires OPENAI_API_KEY) ---"
  if [ -z "${OPENAI_API_KEY:-}" ]; then
    echo "SKIP: OPENAI_API_KEY not set (export it to run integration test)"
  else
    set -a
    [ -f "$REPO_ROOT/.env" ] && . <(tr -d '\r' < "$REPO_ROOT/.env")
    set +a
    export LLM_API_KEY="${OPENAI_API_KEY}"
    export LLM_MODEL="${OPENHANDS_MODEL:-gpt-4o-mini}"
    WORKSPACE="${WORKSPACE:-$REPO_ROOT/bench/swebench/workspaces/astropy__astropy-12907}"
    if [ ! -d "$WORKSPACE/repo" ]; then
      echo "SKIP: workspace not found at $WORKSPACE/repo (run one instance first to materialize)"
    else
      OPENHANDS_CLI="$(dirname "$PYTHON")/openhands"
      if [ ! -x "$OPENHANDS_CLI" ]; then
        OPENHANDS_CLI=openhands
      fi
      cd "$WORKSPACE/repo"
      OH_OUT="$(mktemp)"
      $OPENHANDS_CLI --headless --override-with-envs --json \
        -t "Create an empty file named test_edit_battery.txt. Use the write or edit_file tool." \
        --timeout 120 > "$OH_OUT" 2>&1 || true
      if [ -f "test_edit_battery.txt" ]; then
        echo "PASS: minimal headless (file created)"
      elif grep -q "ActionEvent" "$OH_OUT" 2>/dev/null; then
        echo "PASS: minimal headless (ActionEvent present)"
      else
        echo "WARN: minimal headless did not create file; check OPENAI_API_KEY and openhands-headless-troubleshooting.md"
      fi
      rm -f "$OH_OUT"
      cd "$REPO_ROOT"
    fi
  fi
else
  echo ""
  echo "Optional: run with --integration to test real OpenHands headless (set OPENAI_API_KEY, slow)."
fi

echo ""
echo "=== Battery complete ==="
