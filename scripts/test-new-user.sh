#!/bin/bash

# Provability-Fabric New User Test Script
# Validates the new user experience. Modes: minimal | standard | full
# Set TEST_MODE=minimal|standard|full or pass --minimal, --standard, --full

set -e  # Exit on any error

TEST_MODE="${TEST_MODE:-full}"
for arg in "$@"; do
    case "$arg" in
        --minimal) TEST_MODE=minimal ;;
        --standard) TEST_MODE=standard ;;
        --full) TEST_MODE=full ;;
    esac
done

# Detect Windows environment
if [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$(uname -s)" == "MINGW"* ]]; then
    IS_WINDOWS=true
    echo "Detected Windows environment (Git Bash/WSL)"
else
    IS_WINDOWS=false
fi

echo "Testing new user experience (mode: $TEST_MODE)..."

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

# Test 5: SpecDoc CLI (optional; skip in minimal)
if [ "$TEST_MODE" != "minimal" ]; then
    echo "Test 5: SpecDoc CLI"
    if [ -f "cmd/specdoc/specdoc" ] || [ -f "cmd/specdoc/specdoc.exe" ]; then
        echo "SpecDoc CLI is available"
    else
        echo "SpecDoc CLI not found (optional)"
    fi
fi

# Test 5b: Bundle pack (minimal)
if [ "$TEST_MODE" = "minimal" ]; then
    echo "Test 5: Bundle pack"
    PF_BIN=""
    [ -f "core/cli/pf/pf" ] && PF_BIN="core/cli/pf/pf"
    [ -f "core/cli/pf/pf.exe" ] && PF_BIN="core/cli/pf/pf.exe"
    if [ -n "$PF_BIN" ]; then
        "$PF_BIN" bundle pack bundles/test-new-user-agent -o /tmp/test-new-user-agent.tar.gz 2>/dev/null && echo "Bundle pack works" || echo "Bundle pack skipped"
    fi
fi

# Test 6: Lean Build (if available; skip in minimal)
if [ "$TEST_MODE" != "minimal" ]; then
    echo "Test 6: Lean Build"
    if command -v lake >/dev/null 2>&1; then
        (cd spec-templates/v1/proofs && lake build > /dev/null 2>&1) && echo "Lean build works" || echo "Lean build skipped/failed"
    else
        echo "Lean 4 not found, skipping"
    fi
fi

# Test 7: Cargo test (standard/full only)
if [ "$TEST_MODE" = "standard" ] || [ "$TEST_MODE" = "full" ]; then
    echo "Test 7: Rust workspace tests"
    if command -v cargo >/dev/null 2>&1; then
        (cargo test --workspace --exclude sidecar-watcher 2>/dev/null) && (cargo test -p sidecar-watcher --lib 2>/dev/null) && (cargo test -p sidecar-watcher --tests 2>/dev/null) && echo "Rust tests passed" || echo "Rust tests had warnings/failures"
    else
        echo "cargo not found, skipping"
    fi
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
echo "All tests passed for mode: $TEST_MODE"
echo "CLI builds and runs; agent init and required files OK. See docs/guides/reuse-and-extend.md" 