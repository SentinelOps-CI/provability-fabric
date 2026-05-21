#!/usr/bin/env bash
# Validate a pf benchmark admission bundle against pcs-core schemas (pcs validate compatible).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

BUNDLE_DIR="${1:-benchmark_runs/labtrust_admission}"
CASES="${PCS_BENCHMARK_CASES:-benchmarks/admission/labtrust_qc_release}"
REGISTRY="${PCS_BENCHMARK_REGISTRY:-}"

if [[ -z "${REGISTRY}" ]]; then
  if [[ -n "${PCS_CORE_PATH:-}" && -f "${PCS_CORE_PATH}/examples/artifact_registry.valid.json" ]]; then
    REGISTRY="${PCS_CORE_PATH}/examples/artifact_registry.valid.json"
  elif [[ -f "${ROOT}/../pcs-core/examples/artifact_registry.valid.json" ]]; then
    REGISTRY="${ROOT}/../pcs-core/examples/artifact_registry.valid.json"
  else
    REGISTRY="${ROOT}/tests/pcs/fixtures/labtrust-release/artifact_registry.json"
  fi
fi

# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"
if ! ensure_pf "${ROOT}"; then
  echo "pf not available" >&2
  exit 1
fi

run_materialize_admission_cases "${ROOT}"

PCS_CORE_VALIDATE=(--validate)
if [[ -n "${PCS_CORE_PATH:-}" && -d "${PCS_CORE_PATH}/schemas" ]]; then
  PCS_CORE_VALIDATE+=(--validate-pcs-core-output "${PCS_CORE_PATH}")
elif [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
  PCS_CORE_VALIDATE+=(--validate-pcs-core-output "${ROOT}/../pcs-core")
fi

echo "==> pf benchmark admission --cases ${CASES} ${PCS_CORE_VALIDATE[*]}"
run_pf benchmark admission \
  --cases "${CASES}" \
  --registry "${REGISTRY}" \
  --out "${BUNDLE_DIR}" \
  "${PCS_CORE_VALIDATE[@]}"

PCS_VALIDATE=(go run ./tools/pcs-validate)
if command -v pcs >/dev/null 2>&1 && pcs validate --help >/dev/null 2>&1; then
  PCS_VALIDATE=(pcs validate)
fi

validate_one() {
  local path="$1"
  if [[ "${PCS_VALIDATE[0]}" == "pcs" ]]; then
    pcs validate "${path}"
  else
    go run ./tools/pcs-validate "${path}"
  fi
}

for artifact in \
  "${BUNDLE_DIR}/benchmark_report.v0.json" \
  "${BUNDLE_DIR}/coverage_report.v0.json" \
  "${BUNDLE_DIR}/explain_quality_report.v0.json" \
  "${BUNDLE_DIR}/pcs_bench_ingest.v0.json"
do
  echo "==> validate ${artifact}"
  validate_one "${artifact}"
done

echo "==> validate bundle directory"
PCS_VALIDATE_BUNDLE=(go run ./tools/pcs-validate --benchmark-bundle "${BUNDLE_DIR}")
if [[ -n "${PCS_CORE_PATH:-}" && -d "${PCS_CORE_PATH}/schemas" ]]; then
  PCS_VALIDATE_BUNDLE+=(--pcs-core "${PCS_CORE_PATH}")
elif [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
  PCS_VALIDATE_BUNDLE+=(--pcs-core "${ROOT}/../pcs-core")
fi
"${PCS_VALIDATE_BUNDLE[@]}"

if command -v pcs >/dev/null 2>&1; then
  echo "==> pcs validate ${BUNDLE_DIR}/pcs_bench_ingest.v0.json (schema + semantics)"
  pcs validate "${BUNDLE_DIR}/pcs_bench_ingest.v0.json"
fi

echo "OK: PCS benchmark bundle validated at ${BUNDLE_DIR}"
