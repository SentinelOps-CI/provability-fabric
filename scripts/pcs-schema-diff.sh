#!/usr/bin/env bash
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
    echo "usage: pcs-schema-diff.sh [pcs-core_repo_root]" >&2
    echo "  or set PCS_CORE_PATH / PCS_CORE_SCHEMAS" >&2
    exit 2
  fi
fi

VENDOR_DIR="${ROOT}/config/schemas/pcs"
if [[ ! -d "${CANONICAL}" ]]; then
  echo "pcs-core schemas not found: ${CANONICAL}" >&2
  exit 1
fi
if [[ ! -d "${VENDOR_DIR}" ]]; then
  echo "vendor schemas not found: ${VENDOR_DIR}" >&2
  exit 1
fi

if diff -ru "${CANONICAL}" "${VENDOR_DIR}"; then
  echo "OK: config/schemas/pcs matches ${CANONICAL}"
else
  echo "FAIL: schema drift between pcs-core and provability-fabric" >&2
  exit 1
fi
