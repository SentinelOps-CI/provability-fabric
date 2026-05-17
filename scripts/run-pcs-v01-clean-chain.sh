#!/usr/bin/env bash
# PCS v0.1 full clean-checkout chain (LabTrust-Gym → CertifyEdge → PF → Scientific Memory).
# Requires sibling checkouts; see docs/guides/pcs-v01-clean-chain.md
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PARENT="$(cd "${ROOT}/.." && pwd)"

LABTRUST="${LABTRUST_GYM_ROOT:-${PARENT}/LabTrust-Gym}"
PCS_CORE="${PCS_CORE_PATH:-${PARENT}/pcs-core}"
CERTIFYEDGE="${CERTIFYEDGE_ROOT:-${PARENT}/CertifyEdge}"
SCIENTIFIC_MEMORY="${SCIENTIFIC_MEMORY_ROOT:-${PARENT}/scientific-memory}"

export PCS_DETERMINISTIC="${PCS_DETERMINISTIC:-1}"
export PCS_CORE_PATH="${PCS_CORE}"
export PATH="${ROOT}/scripts:${ROOT}:${PATH}"

CHAIN_LT="${LABTRUST}/examples/pcs_qc_release/scripts/run_pcs_v01_clean_chain.sh"
CHAIN_LT_PS1="${LABTRUST}/examples/pcs_qc_release/scripts/run_pcs_v01_clean_chain.ps1"

if [[ -x "${CHAIN_LT}" ]]; then
  echo "Delegating to LabTrust-Gym: ${CHAIN_LT}"
  exec bash "${CHAIN_LT}" "$@"
fi

if [[ -f "${CHAIN_LT_PS1}" ]] && command -v pwsh >/dev/null 2>&1; then
  echo "Delegating to LabTrust-Gym (PowerShell): ${CHAIN_LT_PS1}"
  exec pwsh -File "${CHAIN_LT_PS1}" "$@"
fi

if [[ -f "${PCS_CORE}/scripts/run-pcs-v01-clean-chain.ps1" ]] && command -v pwsh >/dev/null 2>&1; then
  echo "Delegating to pcs-core → LabTrust-Gym"
  exec pwsh -File "${PCS_CORE}/scripts/run-pcs-v01-clean-chain.ps1" "$@"
fi

# PF-only fallback: run release fixture chain segment (CI / partial checkout)
RELEASE="${ROOT}/tests/pcs/fixtures/labtrust-release"
if [[ -f "${RELEASE}/science_claim_bundle.certified.json" ]]; then
  echo "LabTrust-Gym chain script not found; running PF segment on frozen release fixtures"
  bash "${ROOT}/scripts/pcs-pf-clean-chain.sh" "${RELEASE}"
  if [[ -d "${SCIENTIFIC_MEMORY}" ]] && command -v just >/dev/null 2>&1; then
    echo "== Scientific Memory =="
    (cd "${SCIENTIFIC_MEMORY}" && just pcs-import-bundle "${RELEASE}/signed_science_claim_bundle.json")
    (cd "${SCIENTIFIC_MEMORY}" && just pcs-render-claim claim-pcs-qc-release-v0.1)
  else
    echo "skip Scientific Memory (checkout not found at ${SCIENTIFIC_MEMORY})"
  fi
  echo "OK: PF + optional SM segment (full chain requires LabTrust-Gym at ${LABTRUST})"
  exit 0
fi

echo "PCS v0.1 clean chain requires LabTrust-Gym at:" >&2
echo "  ${CHAIN_LT}" >&2
echo "Clone https://github.com/fraware/LabTrust-Gym beside provability-fabric or set LABTRUST_GYM_ROOT." >&2
exit 2
