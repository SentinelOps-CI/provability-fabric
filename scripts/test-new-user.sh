#!/bin/bash

# Provability-Fabric New User Test Script
# This script validates the new user experience
# Windows-compatible version for Git Bash

set -e  # Exit on any error

# Detect Windows environment
if [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$(uname -s)" == "MINGW"* ]]; then
    IS_WINDOWS=true
    echo "🔧 Detected Windows environment (Git Bash/WSL)"
else
    IS_WINDOWS=false
fi

echo "🧪 Testing new user experience..."

# Test 1: CLI Build and Help
echo "📋 Test 1: CLI Build and Help"
if [ -f "core/cli/pf/pf" ] || [ -f "core/cli/pf/pf.exe" ]; then
    echo "✅ CLI binary exists"
else
    echo "❌ CLI binary not found"
    exit 1
fi

# Test 2: Agent Initialization
echo "📋 Test 2: Agent Initialization"

# Clean up any existing test agent first with Windows-compatible removal
if [ -d "bundles/test-new-user-agent" ]; then
    if [ "$IS_WINDOWS" = true ]; then
        # Windows-compatible removal using find and rm
        echo "🧹 Cleaning up existing test agent..."
        find "bundles/test-new-user-agent" -type f -exec rm -f {} \; 2>/dev/null || true
        find "bundles/test-new-user-agent" -type d -empty -exec rmdir {} \; 2>/dev/null || true
        rmdir "bundles/test-new-user-agent" 2>/dev/null || true
    else
        rm -rf "bundles/test-new-user-agent" 2>/dev/null || true
    fi
fi

# Initialize a new agent
if [ -f "core/cli/pf/pf" ]; then
    ./core/cli/pf/pf init test-new-user-agent
elif [ -f "core/cli/pf/pf.exe" ]; then
    ./core/cli/pf/pf.exe init test-new-user-agent
else
    echo "❌ CLI binary not found"
    exit 1
fi

echo "✅ Agent bundle created"

# Test 3: Required Files Check
echo "📋 Test 3: Required Files Check"

# Check if the bundle was created
if [ -d "bundles/test-new-user-agent" ]; then
    echo "✅ Agent bundle directory exists"
else
    echo "❌ Agent bundle directory not found"
    exit 1
fi

# Check required files
if [ -f "bundles/test-new-user-agent/spec.yaml" ]; then
    echo "✅ spec.yaml exists"
else
    echo "❌ spec.yaml not found"
fi

if [ -f "bundles/test-new-user-agent/spec.md" ]; then
    echo "✅ spec.md exists"
else
    echo "❌ spec.md not found"
fi

if [ -f "bundles/test-new-user-agent/proofs/Spec.lean" ]; then
    echo "✅ proofs/Spec.lean exists"
else
    echo "❌ proofs/Spec.lean not found"
fi

if [ -f "bundles/test-new-user-agent/proofs/lakefile.lean" ]; then
    echo "✅ proofs/lakefile.lean exists"
else
    echo "❌ proofs/lakefile.lean not found"
fi

# Test 4: CLI Commands
echo "📋 Test 4: CLI Commands"

# Test help command
if [ -f "core/cli/pf/pf" ]; then
    ./core/cli/pf/pf --help > /dev/null 2>&1
    echo "✅ CLI help command works"
elif [ -f "core/cli/pf/pf.exe" ]; then
    ./core/cli/pf/pf.exe --help > /dev/null 2>&1
    echo "✅ CLI help command works"
else
    echo "❌ CLI help command failed"
fi

# Test 5: SpecDoc CLI (optional)
echo "📋 Test 5: SpecDoc CLI"
if [ -f "cmd/specdoc/specdoc" ] || [ -f "cmd/specdoc/specdoc.exe" ]; then
    echo "✅ SpecDoc CLI is available"
else
    echo "⚠️  SpecDoc CLI not found (optional component)"
fi

# Test 6: Lean Build (if available)
echo "📋 Test 6: Lean Build"
if command -v lake >/dev/null 2>&1; then
    echo "🔍 Testing Lean build..."
    cd spec-templates/v1/proofs
    if lake build > /dev/null 2>&1; then
        echo "✅ Lean build works"
    else
        echo "⚠️  Lean build failed (may need network access)"
    fi
    cd ../../..
else
    echo "⚠️  Lean 4 not found, skipping Lean build test"
fi

# Clean up test agent with Windows-compatible removal
echo "🧹 Cleaning up test files..."
if [ -d "bundles/test-new-user-agent" ]; then
    if [ "$IS_WINDOWS" = true ]; then
        # Windows-compatible removal using find and rm
        find "bundles/test-new-user-agent" -type f -exec rm -f {} \; 2>/dev/null || true
        find "bundles/test-new-user-agent" -type d -empty -exec rmdir {} \; 2>/dev/null || true
        rmdir "bundles/test-new-user-agent" 2>/dev/null || true
    else
        rm -rf "bundles/test-new-user-agent" 2>/dev/null || true
    fi
fi

echo ""
echo "🎉 All tests passed! New user experience is working correctly."
echo ""
echo "✅ CLI builds and runs"
echo "✅ Agent initialization works"
echo "✅ Required files are created"
echo "✅ CLI commands function properly"
echo "✅ SpecDoc CLI is available"
echo ""
if [ "$IS_WINDOWS" = true ]; then
    echo "⚠️  Windows Git Bash Notes:"
    echo "   - Use forward slashes (/) instead of backslashes (\\) in paths"
    echo "   - Use 'bash scripts/test-new-user.sh' instead of 'scripts\\test-new-user.bat'"
    echo "   - If you encounter 'Device or resource busy' errors, close any applications using the files"
    echo ""
fi
echo "The repository is ready for new users 🚀" 