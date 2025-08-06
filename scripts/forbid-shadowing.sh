#!/bin/bash
# SPDX-License-Identifier: Apache-2.0
# Copyright 2025 Provability-Fabric Contributors

set -euo pipefail

echo "🔍 Checking for forbidden shadowing of core DSL definitions..."

SHADOWING_FOUND=0

# Core definitions that should not be redefined outside core
CORE_DEFINITIONS=(
    "inductive Action"
    "def budget_ok"
    "def total_spend"
    "def SpamScore"
    "def BudgetSpend"
    "structure BudgetCfg"
)

# Directories that are allowed to define these (core modules)
ALLOWED_DIRS=(
    "core/lean-libs/"
    "vendor/"
)

# Check for forbidden shadowing
for definition in "${CORE_DEFINITIONS[@]}"; do
    echo "  Checking for shadowing of: $definition"
    
    # Find all occurrences outside allowed directories
    occurrences=$(find . -name "*.lean" -type f | grep -v ".lake" | \
                  grep -v "vendor/" | \
                  grep -v "core/lean-libs/" | \
                  xargs grep -l "$definition" 2>/dev/null || true)
    
    if [ -n "$occurrences" ]; then
        echo "❌ Forbidden shadowing found: $definition"
        echo "   Files:"
        echo "$occurrences" | sed 's/^/     - /'
        echo ""
        SHADOWING_FOUND=1
    else
        echo "✅ No shadowing of: $definition"
    fi
done

# Check for proper imports from core DSL
echo ""
echo "🔍 Checking for proper imports from core DSL..."

LEAN_FILES=$(find bundles -name "*.lean" -type f | grep -v ".lake" || true)

for file in $LEAN_FILES; do
    if grep -q "import Fabric" "$file"; then
        echo "✅ $file imports from core DSL"
    else
        echo "⚠️  $file does not import from core DSL"
        # This is not necessarily an error, but worth noting
    fi
done

# Final report
echo ""
if [ $SHADOWING_FOUND -eq 0 ]; then
    echo "✅ No forbidden shadowing found!"
    echo "✅ All core definitions are properly centralized"
    exit 0
else
    echo "❌ Forbidden shadowing detected!"
    echo ""
    echo "💡 Recommendations:"
    echo "  1. Remove duplicate definitions from bundle files"
    echo "  2. Import from core DSL instead of redefining"
    echo "  3. Use parametrized functions with CFG instead of hardcoded values"
    echo "  4. Keep only agent-specific logic in bundle files"
    exit 1
fi 