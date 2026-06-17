#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

PF="${PF:-./core/cli/pf/pf}"
if [[ -f "./core/cli/pf/pf.exe" ]]; then
  PF="./core/cli/pf/pf.exe"
elif [[ ! -x "$PF" && ! -f "$PF" ]]; then
  (cd core/cli/pf && go build -o pf .)
  PF="./core/cli/pf/pf"
fi

EXAMPLE="specs/evidence/v0.1/examples/valid"
BUNDLE="$EXAMPLE/basic-evidence-bundle.json"

"$PF" evidence validate "$BUNDLE" --strict --base-dir "$EXAMPLE"
mkdir -p testbed/evidence-v0.1/out
"$PF" evidence replay --bundle "$BUNDLE" --base-dir "$EXAMPLE" --out testbed/evidence-v0.1/out/replay-report.json
echo "evidence-v0.1 happy path OK"
