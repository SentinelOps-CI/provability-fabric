#!/usr/bin/env bash
# Freeze LabTrust + CertifyEdge release fixtures (pcs-core examples/labtrust-release certified bundle).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
RELEASE="${ROOT}/tests/pcs/fixtures/labtrust-release"
PCS_CORE="${PCS_CORE_PATH:-${ROOT}/../pcs-core}"
CERTIFIED_SRC="${PCS_CORE}/examples/labtrust-release/science_claim_bundle.certified.json"
CERTIFIED="${RELEASE}/science_claim_bundle.certified.json"
VR="${RELEASE}/verification_result.json"
SIGNED="${RELEASE}/signed_science_claim_bundle.json"

mkdir -p "${RELEASE}"
if [[ -f "${CERTIFIED_SRC}" ]]; then
  cp "${CERTIFIED_SRC}" "${CERTIFIED}"
  echo "Copied certified bundle from pcs-core"
fi

export PF_SOURCE_COMMIT="${PF_SOURCE_COMMIT:-cccccccccccccccccccccccccccccccccccccccc}"
cd "${ROOT}/core/cli/pf"
go run . verify science-claim "${CERTIFIED}" --out "${VR}"
go run . sign science-claim "${CERTIFIED}" --out "${SIGNED}"
go run . inspect science-claim "${SIGNED}" --strict
go run . validate verification-result "${VR}"
go run . validate signed-science-claim "${SIGNED}"
echo "OK: labtrust-release fixtures frozen under ${RELEASE}"
