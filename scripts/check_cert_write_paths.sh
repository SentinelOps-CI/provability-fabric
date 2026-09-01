#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Fail if direct CERT writers appear outside the two expected bridge points.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CERT_WRITER_FILE="runtime/sidecar-watcher/src/cert_v1.rs"
EXPECTED_DEFINITION='pub fn write_cert(cert: &CertV1, session: &str, seq: u64) -> Result<String> {'
EXPECTED_BOUND_CALL='    let path = write_cert(cert, session, seq)?;'

if ! command -v git >/dev/null 2>&1; then
  echo "check_cert_write_paths: git is required" >&2
  exit 127
fi

matches="$(mktemp)"
trap 'rm -f "$matches"' EXIT

# git grep returns 0 when it finds matches, 1 when there are no matches, and
# >1 on an actual scan error. Only the no-match case is non-fatal: a scanner
# failure must never collapse into a successful guard result.
set +e
git grep -n -w 'write_cert' -- \
  ':(glob)runtime/*.rs' \
  ':(glob)runtime/**/*.rs' >"$matches"
scan_status=$?
set -e
if [[ "$scan_status" -gt 1 ]]; then
  echo "check_cert_write_paths: scan failed with status $scan_status" >&2
  exit "$scan_status"
fi

violations=0
definition_count=0
bound_call_count=0
while IFS= read -r line; do
  file="${line%%:*}"
  # Normalize Windows path separators from scanner output.
  file="${file//\\//}"
  remainder="${line#*:}"
  content="${remainder#*:}"

  if [[ "$file" == "$CERT_WRITER_FILE" && "$content" == "$EXPECTED_DEFINITION" ]]; then
    definition_count=$((definition_count + 1))
    if [[ "$definition_count" -eq 1 ]]; then
      continue
    fi
  fi
  if [[ "$file" == "$CERT_WRITER_FILE" && "$content" == "$EXPECTED_BOUND_CALL" ]]; then
    bound_call_count=$((bound_call_count + 1))
    if [[ "$bound_call_count" -eq 1 ]]; then
      continue
    fi
  fi

  echo "CERT write without binding hook: $line" >&2
  violations=$((violations + 1))
done <"$matches"

if [[ "$definition_count" -ne 1 ]]; then
  echo "check_cert_write_paths: expected exactly one write_cert definition, found $definition_count" >&2
  violations=$((violations + 1))
fi
if [[ "$bound_call_count" -ne 1 ]]; then
  echo "check_cert_write_paths: expected exactly one bound write_cert call, found $bound_call_count" >&2
  violations=$((violations + 1))
fi

if [[ "$violations" -gt 0 ]]; then
  echo "check_cert_write_paths: $violations violation(s)" >&2
  exit 1
fi

echo "check_cert_write_paths: OK"
