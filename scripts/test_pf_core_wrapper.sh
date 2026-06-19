#!/usr/bin/env bash
# Smoke test pf core wrapper against pinned schemas (Phase 7 PR-3).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
bash "$ROOT/scripts/init_pf_core_vendor.sh"
pip install -q -e "$ROOT/tools/pf-core" jsonschema referencing
bash "$ROOT/scripts/pf-core.sh" core schema-check --schemas "$ROOT/vendor/pf-core/schemas"
echo "OK: pf core wrapper schema-check"
