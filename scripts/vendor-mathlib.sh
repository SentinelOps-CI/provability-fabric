#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

echo "Vendoring mathlib for offline builds..."
echo "vendor-mathlib start $(date -u +%Y-%m-%dT%H:%M:%SZ)"

# Configuration
MATHLIB_VERSION="v4.7.0"
MATHLIB_COMMIT="a45ae63747140c1b2cbad9d46f518015c047047a"
VENDOR_DIR="vendor/mathlib"

# Create vendor directory
mkdir -p "$VENDOR_DIR"

# Drop partial cache trees (e.g. restored .git without build artifacts)
if [ -d "$VENDOR_DIR/.git" ] && [ ! -d "$VENDOR_DIR/.lake/build/lib" ]; then
    echo "Partial mathlib cache (no build artifacts); refreshing vendor tree..."
    rm -rf "$VENDOR_DIR"
fi

# Preserve lake artifacts when Actions restores .lake without .git
LAKE_BACKUP=""
if [ -d "$VENDOR_DIR/.lake/build/lib" ] && [ -n "$(ls -A "$VENDOR_DIR/.lake/build/lib" 2>/dev/null || true)" ] \
   && [ ! -d "$VENDOR_DIR/.git" ]; then
    LAKE_BACKUP=$(mktemp -d)
    echo "Preserving restored mathlib .lake across fresh clone..."
    mv "$VENDOR_DIR/.lake" "$LAKE_BACKUP/lake"
    rm -rf "$VENDOR_DIR"
fi

# Clone mathlib to vendor directory (remove stale cache dirs missing .git)
echo "Cloning mathlib $MATHLIB_VERSION to $VENDOR_DIR..."
if [ ! -d "$VENDOR_DIR/.git" ] || [ ! -f "$VENDOR_DIR/lakefile.lean" ]; then
    rm -rf "$VENDOR_DIR"
    if ! timeout 600 git clone --depth 1 --branch "$MATHLIB_VERSION" \
        https://github.com/leanprover-community/mathlib4.git "$VENDOR_DIR"; then
        echo "git clone timed out after 10 minutes"
        exit 1
    fi
else
    echo "Mathlib already exists in vendor directory"
fi

if [ -n "$LAKE_BACKUP" ] && [ -d "$LAKE_BACKUP/lake" ]; then
    rm -rf "$VENDOR_DIR/.lake"
    mv "$LAKE_BACKUP/lake" "$VENDOR_DIR/.lake"
    rm -rf "$LAKE_BACKUP"
    echo "Restored preserved mathlib .lake"
fi

# Verify the correct commit
cd "$VENDOR_DIR"
CURRENT_COMMIT=$(git rev-parse HEAD)
if [ "$CURRENT_COMMIT" != "$MATHLIB_COMMIT" ]; then
    echo "Warning: Expected commit $MATHLIB_COMMIT, got $CURRENT_COMMIT"
    echo "Checking out correct commit..."
    if ! timeout 300 git fetch --depth 1 origin "$MATHLIB_COMMIT"; then
        echo "git fetch timed out after 5 minutes"
        exit 1
    fi
    git checkout "$MATHLIB_COMMIT"
fi

# Populate .olean files (prefer Mathlib's prebuilt cache over a full compile)
echo "Fetching mathlib build artifacts..."
# A nonempty build directory may contain partial artifacts. Invoke the
# cache client even after restoring an Actions cache.
# Three bounded attempts fit inside the former 15-minute download budget.
if [ "$(git rev-parse HEAD)" != "$MATHLIB_COMMIT" ]; then
  echo "Mathlib revision verification failed" >&2
  exit 1
fi

cache_ready=false
for attempt in 1 2 3; do
  echo "Mathlib cache retrieval attempt $attempt/3"
  if timeout --kill-after=5s 280s lake exe cache get; then
    cache_ready=true
    break
  else
    rc=$?
    echo "Mathlib cache retrieval attempt $attempt failed (exit $rc)" >&2
  fi
  if [ "$attempt" -lt 3 ]; then
    sleep "$((attempt * 5))"
  fi
done

if [ "$cache_ready" != true ]; then
  echo "Mathlib cache retrieval failed after three bounded attempts" >&2
  exit 1
fi
echo "Mathlib cache client completed; downstream builds must still succeed"

echo "Mathlib vendored successfully!"
echo "Location: $VENDOR_DIR"
echo "Commit: $MATHLIB_COMMIT"
echo "Version: $MATHLIB_VERSION"
echo "vendor-mathlib complete $(date -u +%Y-%m-%dT%H:%M:%SZ)"
