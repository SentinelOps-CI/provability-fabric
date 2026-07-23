#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors
#
# Create a local go.work from go.work.example (gitignored).
# Default local DX for multi-module Go work — prefer this over treating
# each go.mod as an isolated island.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

EXAMPLE="${GO_WORK_EXAMPLE:-go.work.example}"
TARGET="${GO_WORK_TARGET:-go.work}"
SYNC=0
FORCE=0

usage() {
  cat <<'EOF'
Usage: scripts/go-work-init.sh [--force] [--sync]

  Copies go.work.example -> go.work (gitignored) for local multi-module Go work.
  Options:
    --force   Overwrite an existing go.work
    --sync    Run `go work sync` after creating go.work
    -h|--help Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --force) FORCE=1 ;;
    --sync) SYNC=1 ;;
    -h|--help) usage; exit 0 ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2
      ;;
  esac
  shift
done

if [[ ! -f "$EXAMPLE" ]]; then
  echo "Missing $EXAMPLE — cannot initialize Go workspace." >&2
  exit 1
fi

if [[ -f "$TARGET" && "$FORCE" -ne 1 ]]; then
  echo "$TARGET already exists (use --force to overwrite from $EXAMPLE)."
else
  cp "$EXAMPLE" "$TARGET"
  echo "Wrote $TARGET from $EXAMPLE"
fi

if [[ "$SYNC" -eq 1 ]]; then
  if ! command -v go >/dev/null 2>&1; then
    echo "go not found on PATH; skipped go work sync" >&2
    exit 1
  fi
  go work sync
  echo "go work sync completed"
fi

echo "Go workspace ready. Primary CLI: core/cli/pf (see CONTRIBUTING.md)."
