#!/usr/bin/env bash
# Regenerate PF-signed LabTrust fixture (deterministic aside from UUIDs/timestamps in output).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUNDLE="${ROOT}/tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json"
OUT="${ROOT}/tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json"

cd "${ROOT}/core/cli/pf"
go run . verify science-claim "${BUNDLE}"
go run . sign science-claim "${BUNDLE}" --out "${OUT}"
go run . inspect science-claim "${OUT}" --strict
echo "OK: wrote ${OUT}"
