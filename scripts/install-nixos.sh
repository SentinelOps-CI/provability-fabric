#!/usr/bin/env bash

# Provability-Fabric Installation Script for NixOS
# This script sets up the development environment for NixOS users
# It checks for required packages and suggests nix-env or configuration.nix additions

set -e  # Exit on any error

echo "🚀 Setting up Provability-Fabric development environment on NixOS..."
echo ""

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Track missing packages for final report
MISSING_PACKAGES=()
NIX_PACKAGES_NEEDED=()

# Function to check if a command exists
check_command() {
    local cmd=$1
    local nix_pkg=$2
    local description=$3
    
    if ! command -v "$cmd" &> /dev/null; then
        echo -e "${RED}❌ $description is not installed${NC}"
        MISSING_PACKAGES+=("$cmd")
        NIX_PACKAGES_NEEDED+=("$nix_pkg")
        return 1
    else
        echo -e "${GREEN}✅ $description found: $(command -v $cmd)${NC}"
        return 0
    fi
}

# Check prerequisites
echo "📋 Checking prerequisites..."
echo ""

# Essential tools
check_command "go" "go" "Go (1.21+)"
GO_AVAILABLE=$?

check_command "python3" "python3" "Python 3"
PYTHON_AVAILABLE=$?

check_command "bash" "bash" "Bash"
check_command "git" "git" "Git"

# Optional tools
echo ""
echo "📋 Checking optional tools..."
check_command "node" "nodejs" "Node.js (for UI components)" || NODE_AVAILABLE=false
check_command "lake" "lean4" "Lean 4 (for formal proofs)" || LEAN_AVAILABLE=false

# If we're missing essential packages, provide NixOS installation instructions
if [ ${#MISSING_PACKAGES[@]} -gt 0 ]; then
    echo ""
    echo -e "${YELLOW}⚠️  Missing packages detected!${NC}"
    echo ""
    echo "You have several options to install the missing packages:"
    echo ""
    echo "Option 1: Add to your configuration.nix:"
    echo "----------------------------------------"
    echo "environment.systemPackages = with pkgs; ["
    for pkg in "${NIX_PACKAGES_NEEDED[@]}"; do
        echo "  $pkg"
    done
    echo "];"
    echo ""
    echo "Then run: sudo nixos-rebuild switch"
    echo ""
    echo "Option 2: Use nix-shell (temporary):"
    echo "------------------------------------"
    echo -n "nix-shell -p"
    for pkg in "${NIX_PACKAGES_NEEDED[@]}"; do
        echo -n " $pkg"
    done
    echo ""
    echo ""
    echo "Option 3: Install with nix-env (user profile):"
    echo "----------------------------------------------"
    for pkg in "${NIX_PACKAGES_NEEDED[@]}"; do
        echo "nix-env -iA nixos.$pkg"
    done
    echo ""
    
    # Exit if essential packages are missing
    if [ $GO_AVAILABLE -ne 0 ] || [ $PYTHON_AVAILABLE -ne 0 ]; then
        echo -e "${RED}Cannot continue without Go and Python. Please install them first.${NC}"
        exit 1
    fi
fi

echo ""
echo "✅ Prerequisites check completed"
echo ""

# Create Python virtual environment for isolated package management
echo "🐍 Setting up Python virtual environment..."

VENV_PATH="./venv"
if [ ! -d "$VENV_PATH" ]; then
    python3 -m venv "$VENV_PATH"
    echo "✅ Created Python virtual environment at $VENV_PATH"
else
    echo "✅ Python virtual environment already exists at $VENV_PATH"
fi

# Activate virtual environment
source "$VENV_PATH/bin/activate"
echo "✅ Activated Python virtual environment"

# Upgrade pip in virtual environment
pip install --upgrade pip > /dev/null 2>&1
echo "✅ Updated pip to latest version"

# Build CLI tools
echo ""
echo "🔨 Building CLI tools..."

# Build pf CLI
if [ -d "core/cli/pf" ]; then
    cd core/cli/pf
    go build -o pf .
    if [ $? -eq 0 ]; then
        echo "✅ Built pf CLI tool"
    else
        echo -e "${YELLOW}⚠️  Failed to build pf CLI - you may need additional Go dependencies${NC}"
    fi
    cd ../../..
else
    echo -e "${YELLOW}⚠️  core/cli/pf directory not found${NC}"
fi

# Build specdoc CLI (optional)
if [ -f "cmd/specdoc/main.go" ]; then
    cd cmd/specdoc
    go build -o specdoc .
    if [ $? -eq 0 ]; then
        echo "✅ Built specdoc CLI tool"
    else
        echo -e "${YELLOW}⚠️  Failed to build specdoc CLI${NC}"
    fi
    cd ../..
else
    echo "⚠️  specdoc CLI not found, skipping"
fi

# Install Python dependencies in virtual environment
echo ""
echo "🐍 Installing Python dependencies in virtual environment..."

install_python_deps() {
    local req_file=$1
    local component=$2
    
    if [ -f "$req_file" ]; then
        echo "Installing $component dependencies..."
        pip install -r "$req_file" > /dev/null 2>&1
        if [ $? -eq 0 ]; then
            echo "✅ Installed $component dependencies"
        else
            echo -e "${YELLOW}⚠️  Some $component dependencies may have failed to install${NC}"
        fi
    fi
}

install_python_deps "tests/integration/requirements.txt" "integration test"
install_python_deps "tests/proof-fuzz/requirements.txt" "proof-fuzz"
install_python_deps "tools/compliance/requirements.txt" "compliance tool"
install_python_deps "tools/insure/requirements.txt" "insurance tool"
install_python_deps "tools/proofbot/requirements.txt" "proofbot"

# Handle Node.js dependencies
if [ "$NODE_AVAILABLE" != false ] && [ -f "marketplace/ui/package.json" ]; then
    echo ""
    echo "📦 Installing Node.js dependencies..."
    cd marketplace/ui
    
    # Use npm with local prefix to avoid global installation issues
    npm install --prefix . > /dev/null 2>&1
    if [ $? -eq 0 ]; then
        echo "✅ Installed UI dependencies locally"
    else
        echo -e "${YELLOW}⚠️  Some Node dependencies may have failed - this is common on NixOS${NC}"
        echo "   You may need to use node2nix or a proper Node development shell"
    fi
    cd ../..
fi

# Test basic functionality
echo ""
echo "🧪 Testing basic functionality..."

# Test pf CLI
if [ -f "core/cli/pf/pf" ]; then
    ./core/cli/pf/pf --help > /dev/null 2>&1
    if [ $? -eq 0 ]; then
        echo "✅ pf CLI is working"
    else
        echo -e "${YELLOW}⚠️  pf CLI built but not functioning properly${NC}"
    fi
else
    echo "❌ pf CLI not found"
fi

# Test agent initialization
if [ -f "core/cli/pf/pf" ]; then
    ./core/cli/pf/pf init test-agent 2>/dev/null
    if [ $? -eq 0 ]; then
        echo "✅ Agent initialization works"
        # Clean up test agent
        rm -rf "bundles/test-agent" 2>/dev/null || true
    else
        echo -e "${YELLOW}⚠️  Agent initialization test failed${NC}"
    fi
fi

# Test Lean build (if Lean is available)
if [ "$LEAN_AVAILABLE" != false ]; then
    echo "🔍 Testing Lean build..."
    if [ -d "spec-templates/v1/proofs" ]; then
        cd spec-templates/v1/proofs
        lake build > /dev/null 2>&1
        if [ $? -eq 0 ]; then
            echo "✅ Lean build works"
        else
            echo -e "${YELLOW}⚠️  Lean build failed - you may need additional Lean packages${NC}"
        fi
        cd ../../..
    fi
fi

echo ""
echo "========================================="
echo ""

if [ ${#MISSING_PACKAGES[@]} -eq 0 ]; then
    echo -e "${GREEN}🎉 Installation completed successfully!${NC}"
else
    echo -e "${YELLOW}🎉 Installation completed with warnings${NC}"
    echo "   Some optional components were skipped due to missing packages"
fi

echo ""
echo "📝 Next steps:"
echo ""
echo "1. Activate the Python virtual environment for each session:"
echo "   source ./venv/bin/activate"
echo ""
echo "2. Add the CLI to your PATH (in your shell configuration):"
echo "   export PATH=\$PATH:$(pwd)/core/cli/pf"
echo ""
echo "3. Initialize an agent:"
echo "   ./core/cli/pf/pf init my-agent"
echo ""
echo "4. Run tests (with venv activated):"
echo "   python tests/trust_fire_orchestrator.py"
echo ""

if [ "$LEAN_AVAILABLE" != false ]; then
    echo "5. For Lean 4 proofs:"
    echo "   cd spec-templates/v1/proofs && lake build"
    echo ""
fi

echo "💡 NixOS Tips:"
echo "   - Always activate the virtual environment before running Python scripts"
echo "   - Consider creating a shell.nix or flake.nix for this project"
echo "   - For persistent development, add tools to your configuration.nix"
echo ""

# Create a convenient activation script
cat > activate.sh << 'EOF'
#!/usr/bin/env bash
# Convenience script to activate the development environment

if [ -f "./venv/bin/activate" ]; then
    source ./venv/bin/activate
    export PATH=$PATH:$(pwd)/core/cli/pf
    echo "✅ Provability-Fabric environment activated"
    echo "   Python venv: $VIRTUAL_ENV"
    echo "   pf CLI available: $(which pf 2>/dev/null || echo 'not in PATH yet')"
else
    echo "❌ Virtual environment not found. Run ./scripts/install-nixos.sh first"
fi
EOF

chmod +x activate.sh
echo "Created ./activate.sh for quick environment activation"