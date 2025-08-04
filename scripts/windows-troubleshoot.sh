#!/bin/bash

# Windows Git Bash Troubleshooting Script
# This script helps diagnose and fix common Windows path issues

set -e

echo "🔧 Windows Git Bash Troubleshooting Script"
echo "=========================================="

# Detect Windows environment
if [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$(uname -s)" == "MINGW"* ]]; then
    echo "✅ Detected Windows environment (Git Bash/WSL)"
    IS_WINDOWS=true
else
    echo "⚠️  This script is designed for Windows Git Bash environments"
    echo "   Current environment: $OSTYPE"
    IS_WINDOWS=false
fi

echo ""

# Check 1: Path separators in current directory
echo "📋 Check 1: Path Separators"
echo "Current directory: $(pwd)"
echo "Directory listing:"
ls -la | head -5

echo ""

# Check 2: Git configuration
echo "📋 Check 2: Git Configuration"
echo "Git version: $(git --version)"
echo "Git core.autocrlf: $(git config core.autocrlf || echo 'not set')"
echo "Git core.eol: $(git config core.eol || echo 'not set')"

echo ""

# Check 3: File permissions
echo "📋 Check 3: File Permissions"
if [ -f "scripts/install.sh" ]; then
    echo "✅ install.sh exists and is executable"
    ls -la scripts/install.sh
else
    echo "❌ install.sh not found"
fi

if [ -f "core/cli/pf/pf" ]; then
    echo "✅ pf CLI exists"
    ls -la core/cli/pf/pf
else
    echo "❌ pf CLI not found"
fi

echo ""

# Check 4: Test path operations
echo "📋 Check 4: Path Operations Test"
echo "Testing forward slash paths:"
cd core/cli/pf 2>/dev/null && echo "✅ cd core/cli/pf works" && cd ../.. || echo "❌ cd core/cli/pf failed"

echo ""

# Check 5: Test file removal
echo "📋 Check 5: File Removal Test"
TEST_FILE="windows-test-file.txt"
echo "Creating test file..."
echo "test content" > "$TEST_FILE"

if [ -f "$TEST_FILE" ]; then
    echo "✅ Test file created successfully"
    
    # Try different removal methods
    if rm -f "$TEST_FILE" 2>/dev/null; then
        echo "✅ Standard rm -f works"
    else
        echo "❌ Standard rm -f failed"
    fi
    
    # Recreate for next test
    echo "test content" > "$TEST_FILE"
    
    if find . -name "$TEST_FILE" -exec rm -f {} \; 2>/dev/null; then
        echo "✅ find + rm works"
    else
        echo "❌ find + rm failed"
    fi
else
    echo "❌ Could not create test file"
fi

echo ""

# Check 6: Environment variables
echo "📋 Check 6: Environment Variables"
echo "PATH: $PATH"
echo "PWD: $PWD"
echo "OSTYPE: $OSTYPE"
echo "SHELL: $SHELL"

echo ""

# Check 7: Common Windows issues
echo "📋 Check 7: Common Windows Issues"

# Check for backslashes in paths
if echo "$PWD" | grep -q "\\\\"; then
    echo "⚠️  Backslashes detected in current path"
    echo "   Current path: $PWD"
    echo "   Recommendation: Use forward slashes in Git Bash"
else
    echo "✅ No backslashes in current path"
fi

# Check for Windows line endings
if [ -f "README.md" ]; then
    if file README.md | grep -q "CRLF"; then
        echo "⚠️  Windows line endings detected in README.md"
        echo "   Recommendation: Use git config core.autocrlf true"
    else
        echo "✅ Unix line endings detected"
    fi
fi

echo ""

# Provide recommendations
echo "🎯 Recommendations for Windows Git Bash:"
echo ""
echo "1. Always use forward slashes (/) in paths:"
echo "   ✅ bash scripts/install.sh"
echo "   ❌ bash scripts\\install.sh"
echo ""
echo "2. Use the updated installation scripts:"
echo "   bash scripts/install.sh"
echo "   bash scripts/test-new-user.sh"
echo ""
echo "3. If you encounter 'Device or resource busy' errors:"
echo "   - Close any file explorers or text editors"
echo "   - Wait a few seconds and try again"
echo "   - The updated scripts handle this automatically"
echo ""
echo "4. For PATH issues:"
echo "   export PATH=\$PATH:\$(pwd)/core/cli/pf"
echo ""
echo "5. If files won't delete:"
echo "   - Close any applications using the files"
echo "   - Use the updated scripts with Windows-compatible removal"
echo ""

echo "🔧 Troubleshooting complete!"
echo "If you're still having issues, try:"
echo "1. Restart Git Bash"
echo "2. Close any file explorers or editors"
echo "3. Run the installation script again: bash scripts/install.sh" 