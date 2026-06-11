#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PF="$ROOT/core/cli/pf/pf"
BUNDLE="$ROOT/specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json"

if [[ ! -x "$PF" ]]; then
  (cd "$ROOT/core/cli/pf" && go build -o pf .)
fi

"$PF" evidence validate "$BUNDLE" --strict
"$PF" evidence replay --bundle "$BUNDLE" --out "$ROOT/testbed/evidence-v0.1/out/replay-report.json"
echo "evidence-v0.1 happy path OK"
