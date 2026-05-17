#!/usr/bin/env bash
# Sync PCS JSON schemas from pcs-core into provability-fabric mirrors.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VENDOR="${1:-${PCS_CORE_PATH:-}}"
CANONICAL="${PCS_CORE_SCHEMAS:-}"

if [[ -z "${CANONICAL}" ]]; then
  if [[ -n "${VENDOR}" && -d "${VENDOR}/schemas" ]]; then
    CANONICAL="${VENDOR}/schemas"
  elif [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
    CANONICAL="${ROOT}/../pcs-core/schemas"
  else
    echo "usage: pcs-schema-sync.sh [pcs-core_repo_root]" >&2
    echo "  or set PCS_CORE_PATH / PCS_CORE_SCHEMAS" >&2
    exit 2
  fi
fi

if [[ ! -d "${CANONICAL}" ]]; then
  echo "pcs-core schemas not found: ${CANONICAL}" >&2
  exit 1
fi

sync_dir() {
  local dest="$1"
  mkdir -p "${dest}"
  if command -v rsync >/dev/null 2>&1; then
    rsync -a --delete "${CANONICAL}/" "${dest}/"
  else
    rm -rf "${dest:?}"/*
    cp -a "${CANONICAL}/." "${dest}/"
  fi
}

sync_dir "${ROOT}/config/schemas/pcs"
sync_dir "${ROOT}/adapters/pcs/schemas"

echo "Synced pcs-core schemas from ${CANONICAL} to:"
echo "  ${ROOT}/config/schemas/pcs"
echo "  ${ROOT}/adapters/pcs/schemas"

PCS_CORE_SCHEMAS="${CANONICAL}" bash "${ROOT}/scripts/pcs-schema-diff.sh"
