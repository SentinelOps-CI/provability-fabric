#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)
REPORT_DIR="$ROOT_DIR/evidence/egress"
mkdir -p "$REPORT_DIR"

echo "# Egress Determinism Report" > "$REPORT_DIR/report.md"
echo >> "$REPORT_DIR/report.md"
echo "Generated: $(date -u)" >> "$REPORT_DIR/report.md"
echo >> "$REPORT_DIR/report.md"

PROFILE_TAG="EGRESS-DET-P1@1.0"
ENV_JSON="$ROOT_DIR/tests/replay/env.json"
KIT_DIR="$ROOT_DIR/external/TRACE-REPLAY-KIT"

echo "Running EGRESS harness for profile $PROFILE_TAG" >> "$REPORT_DIR/report.md"
echo "- Env: $ENV_JSON" >> "$REPORT_DIR/report.md"

set +e
python3 "$KIT_DIR/oracles/lowview_equal.py" \
  --input "$ROOT_DIR/tests/replay/out" \
  --threshold 0.999999 >> "$REPORT_DIR/report.md" 2>&1
RESULT=$?
set -e

if [ $RESULT -ne 0 ]; then
  echo "- Result: FAIL (threshold not met or missing inputs)" >> "$REPORT_DIR/report.md"
  exit 1
else
  echo "- Result: PASS (>= 0.999999 low-view equality)" >> "$REPORT_DIR/report.md"
fi

echo "Report written to $REPORT_DIR/report.md"

