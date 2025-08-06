#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

echo "🔍 Checking for duplicate Lean definitions using AST hashing..."

# Run the AST hash duplicate enforcer
echo "📁 Running AST hash analysis..."
python3 tools/lean_ast_hash.py .

# Capture the exit code
EXIT_CODE=$?

if [ $EXIT_CODE -eq 0 ]; then
    echo ""
    echo "✅ AST hash analysis completed successfully"
    echo "✅ No functional duplicates found"
    exit 0
else
    echo ""
    echo "❌ Functional duplicates detected!"
    echo ""
    echo "💡 Recommendations:"
    echo "  1. Move duplicate definitions to core/lean-libs/ActionDSL.lean"
    echo "  2. Import from core DSL in bundle files"
    echo "  3. Keep only agent-specific logic in bundle files"
    echo "  4. Ensure each bundle has unique theorem names"
    echo ""
    echo "🔍 The AST hash tool detected functionally identical definitions"
    echo "   that differ only in whitespace, comments, or docstrings."
    exit 1
fi 