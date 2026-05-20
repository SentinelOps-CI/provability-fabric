#!/usr/bin/env bash
# Run PCS release admission benchmarks for all workflows (pcs-bench consumable artifacts).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
if ! ensure_pf "${ROOT}"; then
  echo "pf not available; install Go, build core/cli/pf/pf.exe, or set PF=..." >&2
  exit 1
fi

if command -v python3 >/dev/null 2>&1; then
  python3 scripts/materialize-admission-benchmark-cases.py
elif command -v python >/dev/null 2>&1; then
  python scripts/materialize-admission-benchmark-cases.py
else
  echo "python3 or python required to materialize benchmark cases" >&2
  exit 1
fi

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

FAILED=0
TOTAL=0
for SUITE in labtrust_qc_release tool_use_safety computation_reproducibility formal_trust_kernel; do
  TOTAL=$((TOTAL + 1))
  OUT="${OUT_ROOT}/${SUITE}_admission"
  echo "==> pf benchmark admission --cases benchmarks/admission/${SUITE}"
  if ! run_pf benchmark admission \
    --cases "benchmarks/admission/${SUITE}" \
    --registry "${REGISTRY}" \
    --out "benchmark_runs/${SUITE}_admission"; then
    FAILED=$((FAILED + 1))
  fi
done

if [[ "${FAILED}" -ne 0 ]]; then
  echo "admission benchmark: ${FAILED}/${TOTAL} workflow suites failed" >&2
  exit 1
fi
echo "OK: admission benchmarks wrote artifacts under ${OUT_ROOT}"
