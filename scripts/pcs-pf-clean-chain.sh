#!/usr/bin/env bash
# Provability Fabric segment of PCS v0.1 clean-checkout chain.
# Usage: pcs-pf-clean-chain.sh [workdir]
#   workdir must contain science_claim_bundle.certified.json
# Writes verification_result.json and signed_science_claim_bundle.json in workdir.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKDIR="${1:-.}"
WORKDIR="$(cd "${WORKDIR}" && pwd)"
CERTIFIED="${WORKDIR}/science_claim_bundle.certified.json"
VR="${WORKDIR}/verification_result.json"
SIGNED="${WORKDIR}/signed_science_claim_bundle.json"

if [[ -z "${PF:-}" ]]; then
  if [[ -x "${ROOT}/pf" ]]; then
    PF="${ROOT}/pf"
  elif command -v go >/dev/null 2>&1; then
    PF="go -C ${ROOT}/core/cli/pf run ."
  else
    echo "go or ./pf not found; set PF to pf CLI command" >&2
    exit 2
  fi
fi
PCS="${PCS:-${ROOT}/scripts/pcs}"

if [[ ! -f "${CERTIFIED}" ]]; then
  echo "missing certified bundle: ${CERTIFIED}" >&2
  exit 1
fi

export PF_SOURCE_COMMIT="${PF_SOURCE_COMMIT:-$(git -C "${ROOT}" rev-parse HEAD 2>/dev/null || echo cccccccccccccccccccccccccccccccccccccccc)}"

echo "== Provability Fabric: verify =="
${PF} verify science-claim "${CERTIFIED}" --out "${VR}"
echo "== pcs-core: validate verification_result =="
"${PCS}" validate "${VR}"
echo "== Provability Fabric: sign =="
${PF} sign science-claim "${CERTIFIED}" --out "${SIGNED}"
echo "== pcs-core: validate signed bundle =="
"${PCS}" validate "${SIGNED}"
echo "== Provability Fabric: inspect =="
${PF} inspect science-claim "${SIGNED}" --strict
echo "OK: PF clean-chain segment completed in ${WORKDIR}"
