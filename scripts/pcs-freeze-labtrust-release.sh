#!/usr/bin/env bash
# Atomic LabTrust release freeze: PF writes release-run/, then promotes to all targets.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

bash "${ROOT}/scripts/pcs-release-run-pf.sh"
bash "${ROOT}/scripts/pcs-release-run-promote.sh"
