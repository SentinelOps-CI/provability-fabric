#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PF="$ROOT/core/cli/pf/pf"
TAMPER="$ROOT/specs/evidence/v0.1/examples/invalid/bad-bundle-digest.json"

if [[ ! -x "$PF" ]]; then
  (cd "$ROOT/core/cli/pf" && go build -o pf .)
fi

set +e
"$PF" evidence validate "$TAMPER" --strict
code=$?
set -e
if [[ "$code" -eq 0 ]]; then
  echo "expected tamper validation failure" >&2
  exit 1
fi
echo "evidence-v0.1 tamper case OK"
