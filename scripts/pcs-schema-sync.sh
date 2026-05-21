#!/usr/bin/env bash
# Sync PCS JSON schemas from pcs-core into provability-fabric mirrors.
# Preserves PF-only schemas (admission benchmarks, computation bundle, profiles).
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

PF_ONLY=(
  "AdmissionBenchmarkCase.v0.schema.json"
  "PCSBenchIngest.v0.schema.json"
  "ScienceClaimBundle.computation.v0.schema.json"
)
PF_ONLY_PROFILES=(
  "ScienceClaimBundle.computation.v0.schema.json"
)

STAGING="$(mktemp -d 2>/dev/null || mktemp -d -t pf-pcs-schema-sync)"
trap 'rm -rf "${STAGING}"' EXIT

for name in "${PF_ONLY[@]}"; do
  for dest in "${ROOT}/config/schemas/pcs" "${ROOT}/adapters/pcs/schemas"; do
    if [[ -f "${dest}/${name}" ]]; then
      cp -f "${dest}/${name}" "${STAGING}/${name}"
    fi
  done
done
if [[ -d "${ROOT}/config/schemas/pcs/profiles" ]]; then
  mkdir -p "${STAGING}/profiles"
  for name in "${PF_ONLY_PROFILES[@]}"; do
    if [[ -f "${ROOT}/config/schemas/pcs/profiles/${name}" ]]; then
      cp -f "${ROOT}/config/schemas/pcs/profiles/${name}" "${STAGING}/profiles/${name}"
    fi
  done
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

for name in "${PF_ONLY[@]}"; do
  if [[ -f "${STAGING}/${name}" ]]; then
    cp -f "${STAGING}/${name}" "${ROOT}/config/schemas/pcs/${name}"
    cp -f "${STAGING}/${name}" "${ROOT}/adapters/pcs/schemas/${name}"
  fi
done
if [[ -d "${STAGING}/profiles" ]]; then
  mkdir -p "${ROOT}/config/schemas/pcs/profiles"
  cp -af "${STAGING}/profiles/." "${ROOT}/config/schemas/pcs/profiles/"
fi

echo "Synced pcs-core schemas from ${CANONICAL} to:"
echo "  ${ROOT}/config/schemas/pcs"
echo "  ${ROOT}/adapters/pcs/schemas"
echo "Preserved PF-only: ${PF_ONLY[*]}"

PCS_CORE_SCHEMAS="${CANONICAL}" bash "${ROOT}/scripts/pcs-schema-diff.sh"
