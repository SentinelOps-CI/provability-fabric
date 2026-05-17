#!/usr/bin/env bash
# Regenerate PF-signed LabTrust fixture (deterministic IDs/digests when PF_DETERMINISTIC=1).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck source=_resolve_pf.sh
source "$(dirname "${BASH_SOURCE[0]}")/_resolve_pf.sh"

BUNDLE="${ROOT}/tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json"
OUT="${ROOT}/tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json"

export PF_SOURCE_COMMIT="${PF_SOURCE_COMMIT:-cccccccccccccccccccccccccccccccccccccccc}"
export PF_DETERMINISTIC="${PF_DETERMINISTIC:-1}"
export PCS_DETERMINISTIC="${PCS_DETERMINISTIC:-1}"

if ! ensure_pf "${ROOT}"; then
  exit 2
fi

run_pf verify science-claim "${BUNDLE}"
run_pf sign science-claim "${BUNDLE}" --out "${OUT}"
run_pf inspect science-claim "${OUT}" --strict
echo "OK: wrote ${OUT}"
