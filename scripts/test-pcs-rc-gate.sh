#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export PCS_CORE_PATH="${PCS_CORE_PATH:-${ROOT}/../pcs-core}"
cd "${ROOT}/adapters/pcs"
go test -count=1 -run 'PFLabtrustReleaseFixtureMatchesPCSCoreRC|PFSignedBundleRCIdentity|TestPFAcceptsValidHandoffManifest|TestReleaseChainResultStatusProofCheckedOnValidChain|TestPFHashMatchesPCSCoreSignedBundleVector' ./...
