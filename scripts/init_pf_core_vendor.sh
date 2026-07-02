#!/usr/bin/env bash
# Initialize vendor/pf-core schemas from provability-fabric-core tag (Phase 7 PR-2).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
VENDOR="$ROOT/vendor/pf-core"
PIN_FILE="$VENDOR/PIN"
PF_CORE_REPO="${PF_CORE_REPO:-https://github.com/SentinelOps-CI/provability-fabric-core.git}"
WORK="${TMPDIR:-/tmp}/pf-core-vendor-$$"

TAG="$(sed -n '1p' "$PIN_FILE")"
SHA="$(sed -n '2p' "$PIN_FILE")"

cleanup() { rm -rf "$WORK"; }
trap cleanup EXIT

git clone --depth 1 --branch "$TAG" "$PF_CORE_REPO" "$WORK/repo"
git -C "$WORK/repo" checkout "$SHA" 2>/dev/null || true

rm -rf "$VENDOR/schemas"
mkdir -p "$VENDOR/schemas"
cp -R "$WORK/repo/pf-core/schemas/." "$VENDOR/schemas/"
cp "$WORK/repo/pf-core/VERSION" "$VENDOR/VERSION"

echo "OK: vendor/pf-core schemas at $TAG ($SHA)"
