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
OUT="${EVIDENCE_REPLAY_OUT_DIR:-$(mktemp -d)}"
REPORT="${EVIDENCE_REPLAY_REPORT:-$OUT/replay-report.json}"
mkdir -p "$OUT/replay" "$(dirname "$REPORT")"
REPLAY_CMD=(
  "$PF" evidence replay
  --bundle "$BUNDLE"
  --base-dir "$EXAMPLE"
  --execute
  --low-view
  --out "$REPORT"
  --out-dir "$OUT/replay"
)
printf '%q ' "${REPLAY_CMD[@]}" > "$OUT/replay-command.txt"
printf '\n' >> "$OUT/replay-command.txt"
"${REPLAY_CMD[@]}" 2>&1 | tee "$OUT/deep-replay.log"

python - "$REPORT" <<'PY'
import json
import sys

report = json.load(open(sys.argv[1], encoding="utf-8"))
assert report["status"] == "pass", report
assert report.get("execute_status") == "pass", report
assert report.get("kit_exit_code") == 0, report
assert report.get("kit_second_exit_code") == 0, report
assert report.get("low_view_result") == "pass", report
assert report.get("replay_cert_validation") == "pass", report
PY

test -f "$OUT/replay/replay.cert.json"
test -f "$OUT/replay/replay2.cert.json"
echo "Deep replay execute complete."
echo "Replay report: $REPORT"
echo "Replay artifacts: $OUT/replay"
