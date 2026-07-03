#!/usr/bin/env bash
# Admission / sidecar audit parity vs reference normalize.py (Phase 7 PR-4).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PF_CORE_REF="${PF_CORE_REF:-$ROOT/../provability-fabric-core}"
export PF_CORE_REF

pip install -q pytest 2>/dev/null || python3 -m pip install -q pytest
cd "$ROOT/runtime/sidecar-watcher"
cargo build --quiet --bin emit_observation
cd "$ROOT"
PYTHONPATH="$PF_CORE_REF/pf-core/validator" pytest tests/pf_core_admission_parity/test_sidecar_normalize_parity.py -v
echo "OK: admission/sidecar normalize parity"
