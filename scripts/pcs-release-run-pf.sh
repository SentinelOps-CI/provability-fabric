#!/usr/bin/env bash
# PF segment: verify/sign into release-run/ from LabTrust certified handoff only.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"
# shellcheck source=_resolve_pf_release_admission.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf_release_admission.sh"

PARENT="$(cd "${ROOT}/.." && pwd)"
RUN="${PCS_RELEASE_RUN:-${ROOT}/release-run}"
LABTRUST="${LABTRUST_GYM_ROOT:-${PARENT}/LabTrust-Gym}"
PCS_CORE="${PCS_CORE_PATH:-${PARENT}/pcs-core}"
LT_RELEASE="${LABTRUST}/examples/pcs_qc_release/release"
CERTIFIED_SRC="${LT_RELEASE}/science_claim_bundle.certified.json"
CERTIFIED="${RUN}/science_claim_bundle.certified.json"
VR="${RUN}/verification_result.json"
SIGNED="${RUN}/signed_science_claim_bundle.json"

mkdir -p "${RUN}"
if [[ ! -f "${CERTIFIED_SRC}" ]]; then
  echo "error: LabTrust certified handoff not found: ${CERTIFIED_SRC}" >&2
  exit 1
fi
if ! HANDOFF_SRC="$(resolve_pf_handoff "${LT_RELEASE}" "${PCS_CORE}")"; then
  echo "error: HandoffManifest.v0 not found under ${LT_RELEASE} or ${PCS_CORE}/examples/labtrust-release" >&2
  exit 1
fi
if ! REGISTRY_SRC="$(resolve_pf_registry "${LT_RELEASE}" "${PCS_CORE}" "${ROOT}")"; then
  echo "error: ArtifactRegistry.v0 not found for release-mode PF" >&2
  exit 1
fi

PF_SOURCE_COMMIT="$(git -C "${ROOT}" rev-parse HEAD)"
export PF_SOURCE_COMMIT PF_RELEASE_MODE=1 PF_DETERMINISTIC="${PF_DETERMINISTIC:-1}"

cp -f "${CERTIFIED_SRC}" "${CERTIFIED}"
echo "== PF release-run: certified bundle from LabTrust handoff =="

if ! ensure_pf "${ROOT}"; then
  exit 2
fi

run_pf verify science-claim "${CERTIFIED}" \
  --release-mode --handoff "${HANDOFF_SRC}" --registry "${REGISTRY_SRC}" --out "${VR}"
run_pf sign science-claim "${CERTIFIED}" \
  --release-mode --handoff "${HANDOFF_SRC}" --registry "${REGISTRY_SRC}" --out "${SIGNED}"
run_pf inspect science-claim "${SIGNED}" --strict

python3 "${ROOT}/scripts/pcs-release-run-validate.py" "${RUN}"

echo "OK: PF artifacts in ${RUN} (pf_commit=${PF_SOURCE_COMMIT})"
