#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PF="$ROOT/core/cli/pf/pf"
BUNDLE="$ROOT/specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json"

if [[ ! -x "$PF" ]]; then
  (cd "$ROOT/core/cli/pf" && go build -o pf .)
fi

"$PF" evidence validate "$BUNDLE" --strict --base-dir "$ROOT/specs/evidence/v0.1/examples/valid"
mkdir -p "$ROOT/testbed/evidence-v0.1/out"
"$PF" evidence replay --bundle "$BUNDLE" --base-dir "$ROOT/specs/evidence/v0.1/examples/valid" --out "$ROOT/testbed/evidence-v0.1/out/replay-report.json"
echo "evidence-v0.1 happy path OK"
