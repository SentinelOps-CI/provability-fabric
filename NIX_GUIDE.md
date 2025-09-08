# NixOS Development Guide for Provability-Fabric

This guide provides instructions for setting up and developing Provability-Fabric on NixOS systems.

## Prerequisites

### Required Packages

Add the following to your `configuration.nix`:

```nix
environment.systemPackages = with pkgs; [
  go
  python3
  git
  bash
];
```

### Optional Packages

```nix
environment.systemPackages = with pkgs; [
  nodejs           # For UI components
  lean4           # For formal proof verification
];
```

After updating `configuration.nix`, rebuild your system:
```bash
sudo nixos-rebuild switch
```

### Alternative: Temporary Shell Environment

For a temporary development environment without system changes:

```bash
nix-shell -p go python3 git bash nodejs lean4
```

## Installation

### Quick Setup

Run the NixOS-specific installation script:

```bash
./scripts/install-nixos.sh
```

This script will:
- Check for all required dependencies
- Create a Python virtual environment (avoiding NixOS pip restrictions)
- Build the `pf` CLI tool
- Install Python dependencies in the virtual environment
- Create an activation script for future sessions

### Manual Setup

If you prefer manual installation:

1. **Create Python virtual environment:**
   ```bash
   python3 -m venv venv
   source venv/bin/activate
   ```

2. **Build the pf CLI:**
   ```bash
   cd core/cli/pf
   go build -o pf .
   cd ../../..
   ```

3. **Install Python dependencies:**
   ```bash
   source venv/bin/activate
   pip install -r tests/integration/requirements.txt
   pip install -r tools/compliance/requirements.txt
   pip install -r tools/proofbot/requirements.txt
   ```

4. **Add to PATH:**
   ```bash
   export PATH=$PATH:$(pwd)/core/cli/pf
   ```

## Daily Development Workflow

### Activating the Environment

Use the convenience script created during installation:

```bash
source ./activate.sh
```

Or manually:

```bash
source venv/bin/activate
export PATH=$PATH:$(pwd)/core/cli/pf
```

### Running Commands

With the environment activated:

```bash
# Initialize an agent
pf init my-agent

# Run tests
python tests/trust_fire_orchestrator.py

# Build Lean proofs (if Lean4 is installed)
cd spec-templates/v1/proofs && lake build
```

## Common Issues and Solutions

### Issue: `pip install` fails globally

**Solution:** Always use the virtual environment:
```bash
source venv/bin/activate
pip install <package>
```

### Issue: `/bin/bash` not found

**Solution:** Scripts should use `#!/usr/bin/env bash` or run with:
```bash
bash ./scripts/script-name.sh
```

### Issue: Node.js global packages fail

**Solution:** Install locally with prefix:
```bash
npm install --prefix ./marketplace/ui
```

### Issue: Go build fails with linking errors

**Solution:** Ensure all C dependencies are available:
```bash
nix-shell -p gcc pkg-config
```

### Issue: `rootCmd` undefined error in pf CLI

**Solution:** This has been fixed in the codebase. The `rootCmd` is now properly declared as a package-level variable.

## Development Tips

### Using Nix Flakes (Advanced)

Create a `flake.nix` for reproducible development:

```nix
{
  description = "Provability-Fabric development environment";
  
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };
  
  outputs = { self, nixpkgs }: {
    devShells.x86_64-linux.default = nixpkgs.legacyPackages.x86_64-linux.mkShell {
      buildInputs = with nixpkgs.legacyPackages.x86_64-linux; [
        go
        python3
        python3Packages.pip
        python3Packages.virtualenv
        nodejs
        lean4
        git
      ];
      
      shellHook = ''
        echo "Provability-Fabric development environment"
        if [ -f "./venv/bin/activate" ]; then
          source ./venv/bin/activate
        fi
        export PATH=$PATH:$(pwd)/core/cli/pf
      '';
    };
  };
}
```

Then use:
```bash
nix develop
```

### Creating a Shell.nix

For non-flake users, create `shell.nix`:

```nix
{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  buildInputs = with pkgs; [
    go
    python3
    python3Packages.pip
    python3Packages.virtualenv
    nodejs
    lean4
    git
  ];
  
  shellHook = ''
    echo "Entering Provability-Fabric development environment"
    if [ ! -d "venv" ]; then
      python3 -m venv venv
    fi
    source venv/bin/activate
    export PATH=$PATH:$(pwd)/core/cli/pf
  '';
}
```

Use with:
```bash
nix-shell
```

## Testing the Installation

Run these commands to verify your setup:

```bash
# Check pf CLI
./core/cli/pf/pf --help

# Test agent initialization
./core/cli/pf/pf init test-agent
rm -rf bundles/test-agent

# Check Python environment
source venv/bin/activate
python -c "import yaml; print('Python dependencies OK')"

# Check Go build
cd core/cli/pf && go build -o pf . && echo "Go build OK"
```

## Maintaining the Environment

### Updating Dependencies

```bash
# Update Python packages
source venv/bin/activate
pip install --upgrade -r tests/integration/requirements.txt

# Update Go modules
cd core/cli/pf
go get -u ./...
go mod tidy
```

### Cleaning Up

```bash
# Remove virtual environment
rm -rf venv/

# Clean Go build cache
go clean -cache

# Remove built binaries
rm -f core/cli/pf/pf
```

## NixOS-Specific Features

The `install-nixos.sh` script includes:

1. **Colored output** for clear status indication
2. **Dependency checking** with exact Nix package suggestions
3. **Virtual environment** for Python package isolation
4. **Local installations** for Node.js packages
5. **Activation script** for quick environment setup

## Troubleshooting Commands

```bash
# Check which packages are installed
nix-env -q | grep -E "go|python|node|lean"

# Find Nix package names
nix search nixpkgs go
nix search nixpkgs python3
nix search nixpkgs nodejs

# Check current PATH
echo $PATH | tr ':' '\n'

# Verify virtual environment is active
echo $VIRTUAL_ENV
```

## Additional Resources

- [NixOS Python Guide](https://nixos.wiki/wiki/Python)
- [NixOS Go Guide](https://nixos.wiki/wiki/Go)
- [Nix Flakes Documentation](https://nixos.wiki/wiki/Flakes)
- [Provability-Fabric Documentation](./README.md)

## Support

If you encounter NixOS-specific issues:

1. Check this guide first
2. Ensure all prerequisites are installed
3. Try the manual setup steps
4. Create an issue with NixOS-specific details

Remember: NixOS's declarative and immutable approach requires different strategies than traditional Linux distributions, but provides better reproducibility and system stability.