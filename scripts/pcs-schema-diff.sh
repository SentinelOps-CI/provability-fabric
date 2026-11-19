#!/usr/bin/env bash
# Compare provability-fabric config/schemas/pcs to pcs-core (canonical files only; PF extensions allowed).
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
MIRROR_DIR="${ROOT}/adapters/pcs/schemas"
if [[ ! -d "${CANONICAL}" ]]; then
  echo "pcs-core schemas not found: ${CANONICAL}" >&2
  exit 1
fi
if [[ ! -d "${VENDOR_DIR}" || ! -d "${MIRROR_DIR}" ]]; then
  echo "schema mirror directories missing" >&2
  exit 1
fi

FAILED=0
CANONICAL_COUNT=0
for path in "${CANONICAL}"/*.json; do
  [[ -f "${path}" ]] || continue
  CANONICAL_COUNT=$((CANONICAL_COUNT + 1))
  name="$(basename "${path}")"
  vendor_path="${VENDOR_DIR}/${name}"
  if [[ ! -f "${vendor_path}" ]]; then
    case "${name}" in
      PcsBenchIngest.v0.schema.json)
        if [[ -f "${VENDOR_DIR}/PCSBenchIngest.v0.schema.json" ]]; then
          vendor_path="${VENDOR_DIR}/PCSBenchIngest.v0.schema.json"
        fi
        ;;
    esac
  fi
  if [[ ! -f "${vendor_path}" ]]; then
    echo "missing vendor schema: ${name}" >&2
    FAILED=1
    continue
  fi
  if ! diff -u "${path}" "${vendor_path}"; then
    FAILED=1
  fi
done

if [[ "${CANONICAL_COUNT}" -eq 0 ]]; then
  echo "canonical schema directory contains no JSON schemas" >&2
  FAILED=1
fi

# Both checked-in copies must agree. PF-only profile extensions under
# config/schemas/pcs/profiles are intentionally not mirrored.
for path in "${VENDOR_DIR}"/*.json; do
  [[ -f "${path}" ]] || continue
  name="$(basename "${path}")"
  if [[ ! -f "${MIRROR_DIR}/${name}" ]]; then
    echo "missing adapter schema mirror: ${name}" >&2
    FAILED=1
  elif ! cmp -s "${path}" "${MIRROR_DIR}/${name}"; then
    echo "adapter schema mirror drift: ${name}" >&2
    FAILED=1
  fi
done
for path in "${MIRROR_DIR}"/*.json; do
  [[ -f "${path}" ]] || continue
  name="$(basename "${path}")"
  if [[ ! -f "${VENDOR_DIR}/${name}" ]]; then
    echo "orphaned adapter schema mirror: ${name}" >&2
    FAILED=1
  fi
done

if [[ "${FAILED}" -ne 0 ]]; then
  echo "FAIL: schema drift in canonical or checked-in PCS mirrors" >&2
  exit 1
fi

echo "OK: config/schemas/pcs matches ${CANONICAL} (canonical benchmark/pcs schemas)"
echo "OK: adapters/pcs/schemas matches the checked-in config schema mirror"
for extra in "${VENDOR_DIR}"/*.json; do
  [[ -f "${extra}" ]] || continue
  name="$(basename "${extra}")"
  if [[ ! -f "${CANONICAL}/${name}" ]]; then
    echo "  PF extension preserved: ${name}"
  fi
done
