#!/bin/bash

# Provability-Fabric Installation Script
# This script sets up the development environment for new users
# Modes: --minimal (CLI + bundles only), --standard (+ Rust workspace), --full (all deps)
# Use INSTALL_MODE=minimal|standard|full or pass --minimal, --standard, --full

set -e  # Exit on any error

# Parse install mode from args or env
INSTALL_MODE="${INSTALL_MODE:-full}"
for arg in "$@"; do
    case "$arg" in
        --minimal) INSTALL_MODE=minimal ;;
        --standard) INSTALL_MODE=standard ;;
        --full) INSTALL_MODE=full ;;
    esac
done

# Detect Windows environment
if [[ "$OSTYPE" == "msys" ]] || [[ "$OSTYPE" == "cygwin" ]] || [[ "$(uname -s)" == "MINGW"* ]]; then
    IS_WINDOWS=true
    echo "Detected Windows environment (Git Bash/WSL)"
else
    IS_WINDOWS=false
fi

echo "Setting up Provability-Fabric development environment (mode: $INSTALL_MODE)..."

# Check prerequisites
echo "Checking prerequisites..."

# Check Go (required for all modes)
if ! command -v go &> /dev/null; then
    echo "Go is not installed. Please install Go 1.21+ from https://golang.org/dl/"
    exit 1
fi

# Python required only for full
if [ "$INSTALL_MODE" = "full" ]; then
    if ! command -v python3 &> /dev/null && ! command -v python &> /dev/null; then
        echo "Python is not installed. Please install Python 3.8+ for full install."
        exit 1
    fi
else
    if ! command -v python3 &> /dev/null && ! command -v python &> /dev/null; then
        echo "Python not found (optional for minimal/standard)."
    fi
fi

# Rust required for standard/full
if [ "$INSTALL_MODE" != "minimal" ]; then
    if ! command -v cargo &> /dev/null; then
        echo "Rust/cargo not found. Install from https://rustup.rs/ for standard/full install."
        exit 1
    fi
fi

# Node.js (optional for full)
if command -v node &> /dev/null; then
    NODE_AVAILABLE=true
else
    NODE_AVAILABLE=false
    [ "$INSTALL_MODE" = "full" ] && echo "Node.js not found. UI components will be skipped."
fi

echo "Prerequisites check completed"

# Build CLI tools (all modes)
echo "Building CLI tools..."
cd core/cli/pf
go build -o pf .
echo "Built pf CLI tool"
cd ../../..

# Create bundles dir if missing
mkdir -p bundles

# Build specdoc CLI (optional, skip in minimal if not present)
if [ -f "cmd/specdoc/main.go" ]; then
    cd cmd/specdoc
    go build -o specdoc .
    echo "Built specdoc CLI tool"
    cd ../..
else
    [ "$INSTALL_MODE" != "minimal" ] && echo "specdoc CLI not found, skipping"
fi

# Standard: build Rust workspace
if [ "$INSTALL_MODE" = "standard" ] || [ "$INSTALL_MODE" = "full" ]; then
    echo "Building Rust workspace..."
    if cargo build --workspace 2>/dev/null; then
        echo "Rust workspace built"
    else
        echo "Rust workspace build had warnings or partial failure (optional crates may need extra deps)"
    fi
fi

# Full only: Python and Node dependencies
if [ "$INSTALL_MODE" = "full" ]; then
    echo "Installing Python dependencies..."
    for req in tests/integration/requirements.txt tests/proof-fuzz/requirements.txt tools/compliance/requirements.txt tools/insure/requirements.txt tools/proofbot/requirements.txt; do
        if [ -f "$req" ]; then
            pip install -r "$req" && echo "Installed $req" || true
        fi
    done

    if [ "$NODE_AVAILABLE" = true ] && [ -f "console/package.json" ]; then
        echo "Installing console Node.js dependencies..."
        cd console && npm install --no-audit --no-fund && cd ..
        echo "Installed console dependencies"
    fi
fi

# Test basic functionality
echo "Testing basic functionality..."
if [ -f "core/cli/pf/pf" ]; then PF_BIN="core/cli/pf/pf"; elif [ -f "core/cli/pf/pf.exe" ]; then PF_BIN="core/cli/pf/pf.exe"; else
    PF_BIN=""
fi
[ -z "$PF_BIN" ] && { echo "pf CLI binary not found"; exit 1; }
"$PF_BIN" --help > /dev/null 2>&1
echo "pf CLI is working"
"$PF_BIN" init test-agent
echo "Agent initialization works"

# Lean build test (optional)
if command -v lake &> /dev/null; then
    echo "Testing Lean build..."
    (cd spec-templates/v1/proofs && lake build > /dev/null 2>&1) && echo "Lean build works" || echo "Lean build skipped/failed"
else
    echo "Lean 4 not found, skipping Lean build test"
fi

# Clean up test agent
echo "Cleaning up test files..."
if [ -d "bundles/test-agent" ]; then
    rm -rf "bundles/test-agent" 2>/dev/null || true
    [ "$IS_WINDOWS" = true ] && (find "bundles/test-agent" -type f -exec rm -f {} \; 2>/dev/null; find "bundles/test-agent" -type d -empty -exec rmdir {} \; 2>/dev/null; rmdir "bundles/test-agent" 2>/dev/null) || true
fi

echo ""
echo "Installation completed successfully (mode: $INSTALL_MODE)"
echo ""
echo "Next steps:"
echo "1. Add the CLI to your PATH: export PATH=\$PATH:\$(pwd)/core/cli/pf"
echo "2. Initialize an agent: ./core/cli/pf/pf init my-agent"
[ "$INSTALL_MODE" = "full" ] && echo "3. Run tests: python tests/trust_fire_orchestrator.py"
echo ""
echo "For minimal/standard/full modes, see docs/guides/reuse-and-extend.md"
echo "For Lean 4 proofs: cd spec-templates/v1/proofs && lake build" 