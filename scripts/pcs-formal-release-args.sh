#!/usr/bin/env bash
# Emit pf CLI flags for Lean trust-envelope artifacts when present in a release fixture dir.
# Usage: eval "$(bash scripts/pcs-formal-release-args.sh /path/to/labtrust-release)"
set -euo pipefail

RELEASE_DIR="${1:-}"
if [[ -z "${RELEASE_DIR}" ]]; then
  echo "usage: pcs-formal-release-args.sh <release_fixture_dir>" >&2
  exit 2
fi

PO="${RELEASE_DIR}/proof_obligation.v0.json"
LC="${RELEASE_DIR}/lean_check_result.v0.json"
ARGS=()
if [[ -f "${PO}" ]]; then
  ARGS+=(--proof-obligations "${PO}")
fi
if [[ -f "${LC}" ]]; then
  ARGS+=(--lean-check-result "${LC}")
fi
printf '%q ' "${ARGS[@]}"
printf '\n'
