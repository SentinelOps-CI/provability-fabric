#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

echo "🔧 Vendoring mathlib for offline builds..."

# Configuration
MATHLIB_VERSION="v4.7.0"
MATHLIB_COMMIT="a45ae63747140c1b2cbad9d46f518015c047047a"
VENDOR_DIR="vendor/mathlib"

# Create vendor directory
mkdir -p "$VENDOR_DIR"

# Clone mathlib to vendor directory (remove stale cache dirs missing .git)
echo "📥 Cloning mathlib $MATHLIB_VERSION to $VENDOR_DIR..."
if [ ! -d "$VENDOR_DIR/.git" ]; then
    rm -rf "$VENDOR_DIR"
    git clone --depth 1 --branch "$MATHLIB_VERSION" \
        https://github.com/leanprover-community/mathlib4.git "$VENDOR_DIR"
else
    echo "✅ Mathlib already exists in vendor directory"
fi

# Verify the correct commit
cd "$VENDOR_DIR"
CURRENT_COMMIT=$(git rev-parse HEAD)
if [ "$CURRENT_COMMIT" != "$MATHLIB_COMMIT" ]; then
    echo "⚠️  Warning: Expected commit $MATHLIB_COMMIT, got $CURRENT_COMMIT"
    echo "🔄 Checking out correct commit..."
    git fetch origin "$MATHLIB_VERSION"
    git checkout "$MATHLIB_COMMIT"
fi

# Populate .olean files (prefer Mathlib's prebuilt cache over a full compile)
echo "🔨 Fetching mathlib build artifacts..."
if [ -d .lake/build/lib ] && [ -n "$(ls -A .lake/build/lib 2>/dev/null)" ]; then
  echo "✅ Mathlib build artifacts already present, skipping fetch"
elif timeout 900 lake exe cache get; then
  echo "✅ Downloaded mathlib cache"
else
  echo "❌ Mathlib cache download failed or timed out after 15 minutes"
  echo "   CI should restore vendor/mathlib/.lake from cache; avoid full lake build here."
  exit 1
fi

echo "✅ Mathlib vendored successfully!"
echo "📁 Location: $VENDOR_DIR"
echo "🔗 Commit: $MATHLIB_COMMIT"
echo "🏷️  Version: $MATHLIB_VERSION" 