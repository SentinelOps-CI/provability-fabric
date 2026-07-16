#!/usr/bin/env bash
# EGRESS-DET-P1: pairwise low-view determinism across replay CERT runs.
# Uses TRACE-REPLAY-KIT oracles/lowview_equal.py (positional certs + --min-determinism).
set -euo pipefail

ROOT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")"/.. && pwd)
REPORT_DIR="$ROOT_DIR/evidence/egress"
CERT_DIR="$ROOT_DIR/tests/replay/out/certs"
KIT_ORACLE="$ROOT_DIR/external/TRACE-REPLAY-KIT/oracles/lowview_equal.py"
# Fraction 0.999999 -> percent 99.9999 (oracle --min-determinism)
MIN_DETERMINISM="${LOWVIEW_MIN_DETERMINISM:-99.9999}"
PROFILE_TAG="EGRESS-DET-P1@1.0"

mkdir -p "$REPORT_DIR"

{
  echo "# Egress Determinism Report"
  echo
  echo "Generated: $(date -u)"
  echo
  echo "Profile: $PROFILE_TAG"
  echo "- Cert dir: $CERT_DIR"
  echo "- Oracle: $KIT_ORACLE"
  echo "- min-determinism: $MIN_DETERMINISM"
  echo
} >"$REPORT_DIR/report.md"

if [[ ! -f "$KIT_ORACLE" ]]; then
  echo "- Result: FAIL (missing oracle at $KIT_ORACLE; run make submodules)" >>"$REPORT_DIR/report.md"
  echo "Report written to $REPORT_DIR/report.md"
  exit 1
fi

if [[ ! -d "$CERT_DIR" ]]; then
  echo "- Result: FAIL (missing cert dir $CERT_DIR; run tests/replay/run_replays.sh first)" >>"$REPORT_DIR/report.md"
  echo "Report written to $REPORT_DIR/report.md"
  exit 1
fi

shopt -s nullglob
FAIL=0
COMPARED=0

for bundle_dir in "$ROOT_DIR/tests/replay/bundles"/*; do
  [[ -d "$bundle_dir" ]] || continue
  name=$(basename "$bundle_dir")
  certs=("$CERT_DIR/${name}_run"*.cert.json)

  if [[ ${#certs[@]} -lt 2 ]]; then
    echo "- Bundle $name: FAIL (need >=2 certs for low-view compare, found ${#certs[@]})" >>"$REPORT_DIR/report.md"
    FAIL=1
    continue
  fi

  echo "- Bundle $name: comparing ${#certs[@]} cert(s)" >>"$REPORT_DIR/report.md"
  set +e
  python3 "$KIT_ORACLE" "${certs[@]}" --min-determinism "$MIN_DETERMINISM" >>"$REPORT_DIR/report.md" 2>&1
  RESULT=$?
  set -e
  COMPARED=$((COMPARED + 1))

  if [[ $RESULT -ne 0 ]]; then
    echo "- Bundle $name: FAIL (low-view threshold not met)" >>"$REPORT_DIR/report.md"
    FAIL=1
  else
    echo "- Bundle $name: PASS (>= $MIN_DETERMINISM low-view equality)" >>"$REPORT_DIR/report.md"
  fi
done

if [[ $COMPARED -eq 0 && $FAIL -eq 0 ]]; then
  echo "- Result: FAIL (no replay bundles found under tests/replay/bundles)" >>"$REPORT_DIR/report.md"
  FAIL=1
fi

if [[ $FAIL -ne 0 ]]; then
  echo "- Result: FAIL" >>"$REPORT_DIR/report.md"
  echo "Report written to $REPORT_DIR/report.md"
  exit 1
fi

echo "- Result: PASS" >>"$REPORT_DIR/report.md"
echo "Report written to $REPORT_DIR/report.md"
