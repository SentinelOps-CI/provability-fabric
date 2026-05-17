#!/usr/bin/env bash
# PF segment: verify/sign into release-run/ from LabTrust certified handoff only.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"

PARENT="$(cd "${ROOT}/.." && pwd)"
RUN="${PCS_RELEASE_RUN:-${ROOT}/release-run}"
LABTRUST="${LABTRUST_GYM_ROOT:-${PARENT}/LabTrust-Gym}"
CERTIFIED_SRC="${LABTRUST}/examples/pcs_qc_release/release/science_claim_bundle.certified.json"
HANDOFF_SRC="${LABTRUST}/examples/pcs_qc_release/release/pf_handoff.json"
CERTIFIED="${RUN}/science_claim_bundle.certified.json"
VR="${RUN}/verification_result.json"
SIGNED="${RUN}/signed_science_claim_bundle.json"

mkdir -p "${RUN}"
if [[ ! -f "${CERTIFIED_SRC}" ]]; then
  echo "error: LabTrust certified handoff not found: ${CERTIFIED_SRC}" >&2
  exit 1
fi
if [[ ! -f "${HANDOFF_SRC}" ]]; then
  echo "error: LabTrust pf_handoff.json not found: ${HANDOFF_SRC}" >&2
  exit 1
fi

PF_SOURCE_COMMIT="$(git -C "${ROOT}" rev-parse HEAD)"
export PF_SOURCE_COMMIT PF_RELEASE_MODE=1 PF_DETERMINISTIC="${PF_DETERMINISTIC:-1}"

cp -f "${CERTIFIED_SRC}" "${CERTIFIED}"
echo "== PF release-run: certified bundle from LabTrust handoff =="

if ! ensure_pf "${ROOT}"; then
  exit 2
fi

run_pf verify science-claim "${CERTIFIED}" --release-mode --out "${VR}"
run_pf sign science-claim "${CERTIFIED}" --release-mode --handoff "${HANDOFF_SRC}" --out "${SIGNED}"
run_pf inspect science-claim "${SIGNED}" --strict

python3 "${ROOT}/scripts/pcs-release-run-validate.py" "${RUN}"

echo "OK: PF artifacts in ${RUN} (pf_commit=${PF_SOURCE_COMMIT})"
