#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Evidence v0.2 deep replay testbed (static + optional execute).
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

EXAMPLE="specs/evidence/v0.2/examples/valid"
BUNDLE="$EXAMPLE/deep-replay-bundle.json"

echo "== Step 1: validate v0.2 bundle (strict) =="
"$PF" evidence validate "$BUNDLE" --strict --base-dir "$EXAMPLE"

echo "== Step 2: static replay =="
"$PF" evidence replay --bundle "$BUNDLE" --base-dir "$EXAMPLE"

if [[ "${1:-}" != "--execute" ]]; then
  echo "Static deep replay complete (pass --execute for KIT run)."
  exit 0
fi

if [[ ! -f external/TRACE-REPLAY-KIT/runner/replay_run.py ]]; then
  echo "TRACE-REPLAY-KIT missing — run: make submodules" >&2
  exit 1
fi

echo "== Step 3: execute + low-view =="
# Windows consoles default to a legacy code page; KIT oracles may emit Unicode.
export PYTHONIOENCODING="${PYTHONIOENCODING:-utf-8}"
OUT="$(mktemp -d)"
"$PF" evidence replay --bundle "$BUNDLE" --base-dir "$EXAMPLE" --execute --low-view --out-dir "$OUT/replay"
echo "Deep replay execute complete."
