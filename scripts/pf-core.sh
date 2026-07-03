#!/usr/bin/env bash
# Delegate to pf-core-validator (Phase 7 PR-3).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
export PYTHONPATH="${PYTHONPATH:-}:${ROOT}/tools/pf-core"
exec "$PYTHON" -m pf_core.cli "$@"
