#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Fail if new CERT file writers bypass write_cert_with_binding.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

ALLOWLIST=(
  "runtime/sidecar-watcher/src/cert_v1.rs"
)

violations=0
while IFS= read -r line; do
  file="${line%%:*}"
  skip=0
  for allowed in "${ALLOWLIST[@]}"; do
    if [[ "$file" == "$allowed" ]]; then
      skip=1
      break
    fi
  done
  if [[ "$skip" -eq 1 ]]; then
    continue
  fi
  if [[ "$line" == *"write_cert("* && "$line" != *"write_cert_with_binding"* ]]; then
    echo "CERT write without binding hook: $line" >&2
    violations=$((violations + 1))
  fi
done < <(rg -n 'write_cert\(' runtime --glob '*.rs' || true)

if [[ "$violations" -gt 0 ]]; then
  echo "check_cert_write_paths: $violations violation(s)" >&2
  exit 1
fi

echo "check_cert_write_paths: OK"
