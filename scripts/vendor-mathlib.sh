#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

echo "🔧 Vendoring mathlib for offline builds..."

# Configuration
MATHLIB_VERSION="v4.7.0"
MATHLIB_COMMIT="b5eba595428809e96f3ed113bc7ba776c5f801ac"
VENDOR_DIR="vendor/mathlib"

# Create vendor directory
mkdir -p "$VENDOR_DIR"

# Clone mathlib to vendor directory
echo "📥 Cloning mathlib $MATHLIB_VERSION to $VENDOR_DIR..."
if [ ! -d "$VENDOR_DIR/.git" ]; then
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

# Build mathlib to generate .olean files
echo "🔨 Building mathlib..."
lake build

# Create a lakefile.lean in the vendor directory
cat > "$VENDOR_DIR/lakefile.lean" << 'EOF'
import Lake
open Lake DSL

package mathlib {
  -- add package configuration options here
}

@[default_target]
lean_lib Mathlib {
  -- add library configuration options here
}
EOF

echo "✅ Mathlib vendored successfully!"
echo "📁 Location: $VENDOR_DIR"
echo "🔗 Commit: $MATHLIB_COMMIT"
echo "🏷️  Version: $MATHLIB_VERSION" 