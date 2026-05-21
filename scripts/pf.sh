#!/usr/bin/env bash
# Run the Provability Fabric CLI without a global pf install (Git Bash / WSL / Linux).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "${ROOT}/scripts/_resolve_pf.sh"
if ! ensure_pf "${ROOT}"; then
  exit 1
fi
run_pf "$@"
