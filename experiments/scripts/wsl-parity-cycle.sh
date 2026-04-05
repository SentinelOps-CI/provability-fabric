#!/usr/bin/env bash
# Run in WSL from repo root. Completes: venv (if needed), preflight, orchestration, validation gates, harness, compare, run-ids reminder, delta triage.
set -e
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

echo "=== Docker ==="
docker info || { echo "Enable WSL integration for Docker Desktop and retry."; exit 1; }

echo ""
echo "=== Venv (create + deps) ==="
if [ ! -d .venv ]; then
  python3 -m venv .venv
  .venv/bin/pip install -U pip wheel
  .venv/bin/pip install datasets swebench openhands
fi
source .venv/bin/activate
python -V

echo ""
echo "=== Hard preflight ==="
python experiments/scripts/check_wsl_env.py

echo ""
echo "=== Orchestration (baseline + PF runs, validations, harness, compare, delta triage) ==="
bash experiments/scripts/run-baseline-pf-cycle.sh

echo ""
echo "=== Manual: update run-ids.md with the baseline and PF run IDs printed above ==="
