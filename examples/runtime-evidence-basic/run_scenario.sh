#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Runtime evidence basic scenario: static validation (always) + optional live sidecar emit.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

PF="${PF:-./core/cli/pf/pf}"
if [[ ! -x "$PF" ]]; then
  (cd core/cli/pf && go build -o pf .)
  PF="./core/cli/pf/pf"
fi

EXAMPLE="examples/runtime-evidence-basic"
BUNDLE="$EXAMPLE/basic-evidence-bundle.json"
BINDING="$EXAMPLE/binding-event.json"

echo "== Step 1: static bundle + binding shape =="
"$PF" evidence validate "$BUNDLE" --strict --base-dir "$EXAMPLE"
grep -q '"event_type": "evidence_v01_binding"' "$BINDING"
grep -q '"schema_version": "0.1"' "$BINDING"
grep -q '"artifact_digests"' "$BINDING"
echo "binding-event.json shape OK"

if [[ "${1:-}" != "--live" ]]; then
  echo "Static scenario complete (pass --live for sidecar emit path)."
  exit 0
fi

echo "== Step 2: live sidecar emit (CERT-V1 required) =="
SCHEMA="external/CERT-V1/schema/cert-v1.schema.json"
if [[ ! -f "$SCHEMA" ]]; then
  echo "CERT-V1 schema missing at $SCHEMA — run: make submodules" >&2
  exit 1
fi

cargo test -p sidecar-watcher write_cert_with_binding_emits_binding_jsonl -- --nocapture
echo "Live scenario complete."
