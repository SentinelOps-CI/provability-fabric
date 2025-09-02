#!/bin/bash

# Provability-Fabric Installation Script
# This script sets up the development environment for new users
# Windows-compatible version for Git Bash

set -e  # Exit on any error

# Detect Windows environment
if [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$(uname -s)" == "MINGW"* ]]; then
    IS_WINDOWS=true
    echo "🔧 Detected Windows environment (Git Bash/WSL)"
else
    IS_WINDOWS=false
fi

echo "🚀 Setting up Provability-Fabric development environment..."

# Check prerequisites
echo "📋 Checking prerequisites..."

# Check Go
if ! command -v go &> /dev/null; then
    echo "❌ Go is not installed. Please install Go 1.21+ from https://golang.org/dl/"
    exit 1
fi

# Check Python
if ! command -v python3 &> /dev/null && ! command -v python &> /dev/null; then
    echo "❌ Python is not installed. Please install Python 3.8+"
    exit 1
fi

# Check Node.js (optional)
if ! command -v node &> /dev/null; then
    echo "⚠️  Node.js not found. UI components will be skipped."
    NODE_AVAILABLE=false
else
    NODE_AVAILABLE=true
fi

echo "✅ Prerequisites check completed"

# Build CLI tools
echo "🔨 Building CLI tools..."

cd core/cli/pf
go build -o pf .
echo "✅ Built pf CLI tool"

cd ../../..

# Build specdoc CLI (optional)
if [ -f "cmd/specdoc/main.go" ]; then
    cd cmd/specdoc
    go build -o specdoc .
    echo "✅ Built specdoc CLI tool"
    cd ../..
else
    echo "⚠️  specdoc CLI not found, skipping"
fi

# Install Python dependencies (if requirements.txt files exist)
echo "🐍 Installing Python dependencies..."

if [ -f "tests/integration/requirements.txt" ]; then
    pip install -r tests/integration/requirements.txt
    echo "✅ Installed integration test dependencies"
fi

if [ -f "tests/proof-fuzz/requirements.txt" ]; then
    pip install -r tests/proof-fuzz/requirements.txt
    echo "✅ Installed proof-fuzz dependencies"
fi

if [ -f "tools/compliance/requirements.txt" ]; then
    pip install -r tools/compliance/requirements.txt
    echo "✅ Installed compliance tool dependencies"
fi

if [ -f "tools/insure/requirements.txt" ]; then
    pip install -r tools/insure/requirements.txt
    echo "✅ Installed insurance tool dependencies"
fi

if [ -f "tools/proofbot/requirements.txt" ]; then
    pip install -r tools/proofbot/requirements.txt
    echo "✅ Installed proofbot dependencies"
fi

# Install Node.js dependencies (if available)
if [ "$NODE_AVAILABLE" = true ] && [ -f "marketplace/ui/package.json" ]; then
    echo "📦 Installing Node.js dependencies..."
    cd marketplace/ui
    npm install
    cd ../..
    echo "✅ Installed UI dependencies"
fi

# Test basic functionality
echo "🧪 Testing basic functionality..."

# Test pf CLI
if [ -f "core/cli/pf/pf" ]; then
    ./core/cli/pf/pf --help > /dev/null 2>&1
    echo "✅ pf CLI is working"
else
    echo "❌ pf CLI not found"
    exit 1
fi

# Test agent initialization
./core/cli/pf/pf init test-agent
echo "✅ Agent initialization works"

# Test Lean build (if Lean is available)
if command -v lake &> /dev/null; then
    echo "🔍 Testing Lean build..."
    cd spec-templates/v1/proofs
    lake build > /dev/null 2>&1
    echo "✅ Lean build works"
    cd ../../..
else
    echo "⚠️  Lean 4 not found, skipping Lean build test"
fi

# Clean up test agent with Windows-compatible removal
echo "🧹 Cleaning up test files..."
if [ -d "bundles/test-agent" ]; then
    if [ "$IS_WINDOWS" = true ]; then
        # Windows-compatible removal using find and rm
        find "bundles/test-agent" -type f -exec rm -f {} \; 2>/dev/null || true
        find "bundles/test-agent" -type d -empty -exec rmdir {} \; 2>/dev/null || true
        rmdir "bundles/test-agent" 2>/dev/null || true
    else
        rm -rf "bundles/test-agent"
    fi
fi

echo ""
echo "🎉 Installation completed successfully!"
echo ""
echo "Next steps:"
if [ "$IS_WINDOWS" = true ]; then
    echo "1. Add the CLI to your PATH: export PATH=\$PATH:\$(pwd)/core/cli/pf"
    echo "2. Initialize an agent: ./core/cli/pf/pf init my-agent"
    echo "3. Run tests: python tests/trust_fire_orchestrator.py"
    echo ""
    echo "⚠️  Windows Git Bash Notes:"
    echo "   - Use forward slashes (/) instead of backslashes (\\) in paths"
    echo "   - Use 'bash scripts/install.sh' instead of 'scripts\\install.bat'"
    echo "   - If you encounter 'Device or resource busy' errors, close any applications using the files"
else
    echo "1. Add the CLI to your PATH: export PATH=\$PATH:\$(pwd)/core/cli/pf"
    echo "2. Initialize an agent: ./core/cli/pf/pf init my-agent"
    echo "3. Run tests: python tests/trust_fire_orchestrator.py"
fi
echo ""
echo "For Lean 4 proofs, install Lean and run: cd spec-templates/v1/proofs && lake build" 