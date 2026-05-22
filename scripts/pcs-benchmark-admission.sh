#!/usr/bin/env bash
# Run PCS release admission benchmarks for all workflows (pcs-bench consumable artifacts).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"
if ! ensure_pf "${ROOT}"; then
  echo "pf not available; install Go, build core/cli/pf/pf.exe, or set PF=..." >&2
  exit 1
fi

run_materialize_admission_cases "${ROOT}"

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

OUT_ROOT="${PCS_BENCHMARK_OUT:-${ROOT}/benchmark_runs}"
mkdir -p "${OUT_ROOT}"

PCS_CORE_VALIDATE=()
if [[ -n "${PCS_CORE_PATH:-}" && -d "${PCS_CORE_PATH}/schemas" ]]; then
  PCS_CORE_VALIDATE=(--validate --validate-pcs-core-output "${PCS_CORE_PATH}")
elif [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
  PCS_CORE_VALIDATE=(--validate --validate-pcs-core-output "${ROOT}/../pcs-core")
else
  PCS_CORE_VALIDATE=(--validate)
fi

FAILED=0
TOTAL=0
admission_out_dir() {
  local suite="$1"
  if [[ "${suite}" == "labtrust_qc_release" ]]; then
    echo "labtrust_admission"
  else
    echo "${suite}_admission"
  fi
}

for SUITE in labtrust_qc_release tool_use_safety computation_reproducibility formal_trust_kernel; do
  TOTAL=$((TOTAL + 1))
  OUT_NAME="$(admission_out_dir "${SUITE}")"
  OUT="${OUT_ROOT}/${OUT_NAME}"
  echo "==> pf benchmark admission --cases benchmarks/admission/${SUITE} -> ${OUT_NAME}"
  if ! run_pf benchmark admission \
    --cases "benchmarks/admission/${SUITE}" \
    --registry "${REGISTRY}" \
    --out "benchmark_runs/${OUT_NAME}" \
    "${PCS_CORE_VALIDATE[@]}"; then
    FAILED=$((FAILED + 1))
  fi
done

if [[ "${FAILED}" -ne 0 ]]; then
  echo "admission benchmark: ${FAILED}/${TOTAL} workflow suites failed" >&2
  exit 1
fi
echo "OK: admission benchmarks wrote artifacts under ${OUT_ROOT}"
