#!/usr/bin/env bash
# pcs-bench validate-ingest compatibility wrapper (PF producer ingest + pcs-core release-grade gate).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"

INPUT=""
PCS_CORE=""
BUNDLE_DIR=""
RELEASE_GRADE=0

usage() {
  echo "Usage: $0 --input <pcs_bench_ingest.v0.json> --pcs-core <pcs-core-root> [--bundle-dir <dir>] [--release-grade]" >&2
  exit 2
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --input) INPUT="$2"; shift 2 ;;
    --pcs-core) PCS_CORE="$2"; shift 2 ;;
    --bundle-dir) BUNDLE_DIR="$2"; shift 2 ;;
    --release-grade) RELEASE_GRADE=1; shift ;;
    -h|--help) usage ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
done

[[ -n "${INPUT}" ]] || usage
[[ -n "${PCS_CORE}" ]] || usage

if [[ ! -f "${INPUT}" ]]; then
  echo "missing ingest: ${INPUT}" >&2
  exit 1
fi

if [[ -z "${BUNDLE_DIR}" ]]; then
  BUNDLE_DIR="$(dirname "${INPUT}")"
fi

ensure_pcs_core_python "${PCS_CORE}" || exit 1

PY="$(resolve_python)" || exit 1
ARGS=(--ingest "${INPUT}" --bundle-dir "${BUNDLE_DIR}" --pcs-core "${PCS_CORE}")
if [[ "${RELEASE_GRADE}" -eq 1 ]]; then
  ARGS+=(--release-grade)
fi

exec "${PY}" "${ROOT}/scripts/validate-pf-pcs-bench-ingest.py" "${ARGS[@]}"
