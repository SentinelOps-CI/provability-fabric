#!/usr/bin/env bash
# Freeze LabTrust + CertifyEdge release fixtures for PF verification gate.
# Certified bundle: LabTrust-Gym/examples/pcs_qc_release/release/science_claim_bundle.certified.json
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"

PARENT="$(cd "${ROOT}/.." && pwd)"
RELEASE="${ROOT}/tests/pcs/fixtures/labtrust-release"
LABTRUST="${LABTRUST_GYM_ROOT:-${PARENT}/LabTrust-Gym}"
CERTIFIED_SRC="${LABTRUST}/examples/pcs_qc_release/release/science_claim_bundle.certified.json"
CERTIFIED="${RELEASE}/science_claim_bundle.certified.json"
VR="${RELEASE}/verification_result.json"
SIGNED="${RELEASE}/signed_science_claim_bundle.json"
PCS="${PCS:-${ROOT}/scripts/pcs}"

mkdir -p "${RELEASE}"
if [[ ! -f "${CERTIFIED_SRC}" ]]; then
  echo "error: LabTrust release certified bundle not found: ${CERTIFIED_SRC}" >&2
  echo "Set LABTRUST_GYM_ROOT or clone LabTrust-Gym beside provability-fabric." >&2
  exit 1
fi

cp "${CERTIFIED_SRC}" "${CERTIFIED}"
echo "Copied certified bundle from LabTrust-Gym release"

python3 "${ROOT}/scripts/pcs-freeze-labtrust-release-invalid.py" "${RELEASE}"

export PF_SOURCE_COMMIT="${PF_SOURCE_COMMIT:-cccccccccccccccccccccccccccccccccccccccc}"
export PF_DETERMINISTIC="${PF_DETERMINISTIC:-1}"
export PCS_DETERMINISTIC="${PCS_DETERMINISTIC:-1}"
if ! rebuild_pf "${ROOT}"; then
  echo "hint: run 'make freeze-pcs-labtrust-release' from PowerShell (uses .ps1 fallback)" >&2
  exit 2
fi

run_pf verify science-claim "${CERTIFIED}" --out "${VR}"
run_pf sign science-claim "${CERTIFIED}" --out "${SIGNED}"
run_pf inspect science-claim "${SIGNED}" --strict
run_pf validate verification-result "${VR}"
run_pf validate signed-science-claim "${SIGNED}"

if command -v python3 >/dev/null 2>&1 && [[ -f "${PCS}" ]]; then
  "${PCS}" validate "${CERTIFIED}"
  "${PCS}" validate "${VR}"
  "${PCS}" validate "${SIGNED}"
fi

echo "OK: labtrust-release fixtures frozen under ${RELEASE}"
