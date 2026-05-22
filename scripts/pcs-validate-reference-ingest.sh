#!/usr/bin/env bash
# Validate committed labtrust PcsBenchIngest reference against a producer bundle.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_python.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_python.sh"
PY="$(resolve_python)"

INGEST="${1:-benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json}"
BUNDLE="${2:-benchmark_runs/labtrust_admission}"

exec "${PY}" "${ROOT}/scripts/pcs-bench-producer-contract-check.py" \
  --ingest "${ROOT}/${INGEST}" \
  --bundle-dir "${ROOT}/${BUNDLE}"
