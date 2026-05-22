#!/usr/bin/env bash
# Materialize a reference PcsBenchIngest.v0 for labtrust_qc_release (pcs-core pin / diff audits).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT}"

# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"

ensure_pf "${ROOT}" || exit 1
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

OUT="${ROOT}/benchmark_runs/labtrust_admission"
REF_DIR="${ROOT}/benchmarks/admission/examples"
mkdir -p "${REF_DIR}" "${OUT}"

PCS_CORE_VALIDATE=(--validate)
if [[ -n "${PCS_CORE_PATH:-}" && -d "${PCS_CORE_PATH}/schemas" ]]; then
  PCS_CORE_VALIDATE+=(--validate-pcs-core-output "${PCS_CORE_PATH}")
elif [[ -d "${ROOT}/../pcs-core/schemas" ]]; then
  PCS_CORE_VALIDATE+=(--validate-pcs-core-output "${ROOT}/../pcs-core")
fi

echo "==> pf benchmark admission (labtrust reference ingest)"
run_pf benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry "${REGISTRY}" \
  --out "${OUT}" \
  "${PCS_CORE_VALIDATE[@]}"

REF="${REF_DIR}/labtrust_qc_release.pcs_bench_ingest.reference.json"
cp "${OUT}/pcs_bench_ingest.v0.json" "${REF}"
echo "Wrote ${REF}"

PCS_CORE="${PCS_CORE_PATH:-}"
if [[ -z "${PCS_CORE}" && -d "${ROOT}/../pcs-core/schemas" ]]; then
  PCS_CORE="${ROOT}/../pcs-core"
fi

PY="$(resolve_python)" || exit 1
"${PY}" "${ROOT}/scripts/pcs-bench-producer-contract-check.py" \
  --ingest "${REF}" \
  --bundle-dir "${OUT}"

if [[ -n "${PCS_CORE}" ]]; then
  echo "==> pcs-bench validate-ingest (release-grade)"
  bash "${ROOT}/scripts/pcs-bench-validate-ingest.sh" \
    --input "${REF}" \
    --bundle-dir "${OUT}" \
    --pcs-core "${PCS_CORE}" \
    --release-grade
  bash "${ROOT}/scripts/pcs-bench-validate-ingest.sh" \
    --input "${OUT}/pcs_bench_ingest.v0.json" \
    --bundle-dir "${OUT}" \
    --pcs-core "${PCS_CORE}" \
    --release-grade
fi

if command -v pcs >/dev/null 2>&1; then
  echo "==> pcs validate reference ingest"
  pcs validate "${REF}"
fi

go run ./tools/pcs-validate --benchmark-bundle "${OUT}" ${PCS_CORE_PATH:+--pcs-core "${PCS_CORE_PATH}"}
echo "OK: reference ingest at ${REF}"
