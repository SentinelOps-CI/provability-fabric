#!/usr/bin/env bash
# Linux merge-gate validation checklist (Phase 0 / Wave 7).
# Run on Ubuntu before merging local remediation to main.
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$ROOT_DIR"

echo "=== provability-fabric Linux validation checklist ==="
echo "Repo: $ROOT_DIR"
echo

run_step() {
  echo ">>> $*"
  "$@"
  echo
}

run_step_env() {
  echo ">>> env $*"
  env "$@"
  echo
}

run_step cargo test -p retrieval-gateway
run_step_env PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests

pushd runtime/ledger >/dev/null
run_step npm ci
run_step npm test
run_step npm run typecheck:server
popd >/dev/null

if command -v docker >/dev/null 2>&1; then
  run_step bash tests/replay/test_docker_invocation.sh
else
  echo ">>> SKIP: tests/replay/test_docker_invocation.sh (docker not available)"
  echo
fi

run_step python scripts/count_sidecar_unwraps.py --max 10
run_step python scripts/count_ledger_any.py --max 20
run_step python scripts/audit_ci_honesty.py
run_step python tests/crypto/test_cross_lang_dsse.py
run_step make docs-strict

echo "=== All merge-gate commands passed ==="
