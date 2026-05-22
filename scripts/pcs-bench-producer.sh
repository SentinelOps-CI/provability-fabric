#!/usr/bin/env bash
# PF pcs-bench producer gate: admission benchmark + pcs-core ingest validation for aggregation.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"

ensure_pf "${ROOT}" || exit 1
run_materialize_admission_cases "${ROOT}"

PCS_CORE="${PCS_CORE_PATH:-}"
if [[ -z "${PCS_CORE}" ]]; then
  if [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
    PCS_CORE="${ROOT}/../pcs-core"
  fi
fi
if [[ -z "${PCS_CORE}" || ! -d "${PCS_CORE}/schemas" ]]; then
  echo "PCS_CORE_PATH (or ../pcs-core) with schemas/ is required" >&2
  exit 1
fi

REGISTRY="${PCS_BENCHMARK_REGISTRY:-}"
if [[ -z "${REGISTRY}" ]]; then
  if [[ -f "${PCS_CORE}/examples/artifact_registry.valid.json" ]]; then
    REGISTRY="${PCS_CORE}/examples/artifact_registry.valid.json"
  else
    REGISTRY="${ROOT}/tests/pcs/fixtures/labtrust-release/artifact_registry.json"
  fi
fi

OUT="${PCS_BENCHMARK_OUT:-${ROOT}/benchmark_runs/labtrust_admission}"
mkdir -p "${OUT}"

echo "==> pf benchmark admission (pcs-bench producer)"
run_pf benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry "${REGISTRY}" \
  --out "${OUT}" \
  --validate \
  --validate-pcs-core-output "${PCS_CORE}" \
  --json-summary

INGEST="${OUT}/pcs_bench_ingest.v0.json"
test -f "${INGEST}"

PY="$(resolve_python)" || exit 1

echo "==> pcs-bench validate-ingest (release-grade)"
bash "${ROOT}/scripts/pcs-bench-validate-ingest.sh" \
  --input "${INGEST}" \
  --bundle-dir "${OUT}" \
  --pcs-core "${PCS_CORE}" \
  --release-grade

echo "==> PF producer contract check"
"${PY}" "${ROOT}/scripts/pcs-bench-producer-contract-check.py" \
  --ingest "${INGEST}" \
  --bundle-dir "${OUT}"

if command -v pcs >/dev/null 2>&1; then
  echo "==> pcs validate ${INGEST}"
  pcs validate "${INGEST}"
fi

echo "OK: pcs-bench producer ingest at ${INGEST}"
