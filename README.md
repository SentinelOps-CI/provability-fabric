# Provability-Fabric

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Documentation](https://img.shields.io/badge/docs-latest-brightgreen.svg)](https://provability-fabric.org)
[![TRUST-FIRE](https://img.shields.io/badge/TRUST--FIRE-GA%20Ready-green.svg)](https://github.com/fraware/provability-fabric/actions/workflows/trust-fire-ga-test.yaml)

An open-source framework that binds every AI agent container image to a machine-checkable Lean proof (Proof-of-Behaviour), ensuring provable behavioral guarantees through formal verification.

<p align="center">
  <img src=".github/assets/Provability-Fabric.png" alt="Provability Fabric Logo" width="200"/>
</p>

## Quick Start

### Option 1: Automated Installation (Recommended)

```bash
# Clone the repository
git clone https://github.com/fraware/provability-fabric.git
cd provability-fabric

# Run the installation script
./scripts/install.sh           # For Linux/macOS
scripts/install.bat            # For Windows Command Prompt (RECOMMENDED for Windows)
# Note: Git Bash on Windows may have execution issues

# Test the installation
./scripts/test-new-user.sh     # For Linux/macOS
scripts/test-new-user.bat      # For Windows Command Prompt (RECOMMENDED for Windows)

# Troubleshoot Windows Git Bash issues (if needed)
bash scripts/windows-troubleshoot.sh  # For Windows Git Bash troubleshooting
```

### Option 2: Launch the UI Dashboard

The project includes a React-based marketplace UI for managing AI agent packages and monitoring the system:

```bash
# Navigate to the UI directory
cd marketplace/ui

# Install dependencies (if not already done)
npm install

# Start the development server
npm start

# The UI will be available at http://localhost:3000
```

**UI Features:**
- **Dashboard** - Overview of packages, downloads, and system metrics
- **Package Management** - Browse, search, and install AI agent packages
- **Ledger Integration** - View capsule data and risk scores
- **Health Monitoring** - Quick access to GraphQL API and health checks
- **Real-time Updates** - Live data from the marketplace and ledger services

### Option 3: Manual Installation

```bash
# Clone the repository
git clone https://github.com/fraware/provability-fabric.git
cd provability-fabric

# Build the CLI from source
cd core/cli/pf
go build -o pf .  # On Windows, output is pf.exe

# Add to PATH (Important for Windows users)
# Linux/macOS
export PATH=$PATH:$(pwd)

# Windows (Command Prompt) - RECOMMENDED
set PATH=%PATH%;%CD%

# Windows (PowerShell)
$env:PATH += ";$PWD"

# Go back to repository root
cd ../../..

# Initialize a new agent specification
./pf init my-agent           # Linux/macOS
pf.exe init my-agent         # Windows CMD or PowerShell (RECOMMENDED for Windows)

# Create and verify proofs (must be run from the correct directory)
cd spec-templates/v1/proofs
lake build                   # Requires Lean 4 to be installed
cd ../../../

# Run TRUST-FIRE GA test suite (must be run from repository root)
python tests/trust_fire_orchestrator.py

# Deploy with runtime monitoring (Kubernetes)
# Note: The deployment files are Helm templates and require proper setup
# For testing, you can use the inline deployments from the GitHub workflows:
kubectl apply -f - <<EOF
apiVersion: apps/v1
kind: Deployment
metadata:
  name: attestor
spec:
  replicas: 1
  selector:
    matchLabels:
      app: attestor
  template:
    metadata:
      labels:
        app: attestor
    spec:
      containers:
      - name: attestor
        image: provability-fabric/attestor:test
        ports:
        - containerPort: 8080
        env:
        - name: REDIS_URL
          value: "redis://redis-master:6379"
---
apiVersion: v1
kind: Service
metadata:
  name: attestor-service
spec:
  selector:
    app: attestor
  ports:
  - protocol: TCP
    port: 8080
    targetPort: 8080
EOF
```

## Prerequisites

Before running the installation, ensure you have:

- **Go 1.21+** - For building CLI tools
- **Python 3.8+** - For running tests and scripts
- **Node.js 18+** - For UI components (optional)
- **Lean 4** - For formal proofs (optional, see [Lean installation guide](https://leanprover.github.io/lean4/doc/quickstart.html))
- **kubectl** - For Kubernetes deployment (optional)

## Architecture

Provability-Fabric consists of four core components:

1. **Specification Bundles** - YAML specifications with Lean proofs
2. **Runtime Guards** - Sidecar containers that monitor execution
3. **Solver Adapters** - Verification engines for neural networks and hybrid systems
4. **Marketplace UI** - React-based dashboard for package management and system monitoring

```mermaid
flowchart TD
    A[Agent Specification] --> B[Lean Proof Generation]
    B --> C[Specification Bundle]
    C --> D[Admission Controller]
    D --> E[Container Deployment]
    E --> F[Sidecar Watcher]
    F --> G[Runtime Monitoring]
    G --> H[Constraint Enforcement]

    I[Neural Network] --> J[Marabou Adapter]
    J --> K[Verification Proof]
    K --> C

    L[Hybrid System] --> M[DryVR Adapter]
    M --> N[Reach Set]
    N --> C

    C --> O[Transparency Ledger]
    O --> P[GraphQL API]

    Q[TRUST-FIRE Test Suite] --> R[GA Validation]
    R --> S[Production Ready]

    T[Marketplace UI] --> U[Package Management]
    U --> V[Dashboard Monitoring]
    V --> W[Ledger Integration]

    style A fill:#e1f5fe
    style C fill:#f3e5f5
    style F fill:#fff3e0
    style O fill:#e8f5e8
    style Q fill:#ffebee
    style T fill:#f0f8ff
```

## Components

### Core CLI (`pf`)

- Initialize agent specifications
- Lint and validate proofs
- Sign specification bundles
- Check traceability mappings

### Runtime Components

- **Sidecar Watcher** - Rust-based runtime monitor
- **Admission Controller** - Kubernetes webhook for validation
- **Transparency Ledger** - GraphQL service for audit trail
- **Incident Bot** - Automated incident response and rollback
- **WASM Sandbox** - Secure WebAssembly execution environment
- **Privacy Engine** - Epsilon-differential privacy enforcement
- **Marketplace API** - RESTful API for package management

### Verification Adapters

- **Marabou Adapter** - Neural network verification
- **DryVR Adapter** - Hybrid system reachability analysis

### Lean Libraries

- **ActionDSL** - Reusable action definitions
- **RG** - Rely-Guarantee combinators

### Running Tests

```bash
# Run complete TRUST-FIRE suite (from repository root)
python tests/trust_fire_orchestrator.py

# Run individual phases
python tests/privacy/privacy_burn_down.py --tenant-id acme-beta
python tests/security/malicious_adapter_test.py
python tests/chaos/chaos_rollback_test.py
```

## Production Features

### Security & Compliance

- **SLSA Level 3** - Supply chain security
- **SOC 2 Type II** - Compliance framework
- **Cross-Region DR** - Disaster recovery
- **RBAC** - Role-based access control
- **Network Policies** - Zero-trust networking

### Monitoring & Observability

- **Grafana Dashboards** - Real-time metrics
- **Prometheus** - Time-series monitoring
- **Jaeger** - Distributed tracing
- **Alertmanager** - Incident management

### CI/CD Pipeline

- **GitHub Actions** - Automated testing and deployment
- **Cross-Region Deployment** - Multi-region availability
- **Automated Rollbacks** - Incident response
- **Evidence Collection** - Compliance automation

## Documentation

- [Architecture Overview](docs/index.md)
- [Multi-Tenant Design](docs/multi-tenant.md)
- [Cross-Region DR](docs/cross-region-dr.md)
- [Compliance Framework](docs/compliance/)
- [Security Policies](docs/security/)
- [Operational Excellence](docs/playbooks/)

## Contributing

We welcome contributions! Please see our [Contributing Guide](docs/community/governance.md) for details.

### Development Setup

```bash
# Clone the repository
git clone https://github.com/fraware/provability-fabric.git
cd provability-fabric

# Build CLI tools from source
cd core/cli/pf && go build -o pf.exe . && cd ../..
cd cmd/specdoc && go build -o specdoc.exe . && cd ../..

# Install Python dependencies for testing (if requirements.txt files exist)
if [ -f "tests/integration/requirements.txt" ]; then pip install -r tests/integration/requirements.txt; fi
if [ -f "tests/proof-fuzz/requirements.txt" ]; then pip install -r tests/proof-fuzz/requirements.txt; fi
if [ -f "tools/compliance/requirements.txt" ]; then pip install -r tools/compliance/requirements.txt; fi
if [ -f "tools/insure/requirements.txt" ]; then pip install -r tools/insure/requirements.txt; fi
if [ -f "tools/proofbot/requirements.txt" ]; then pip install -r tools/proofbot/requirements.txt; fi

# Install Node.js dependencies for UI components
cd marketplace/ui && npm install && cd ../..

# Start the UI development server (optional)
cd marketplace/ui && npm start
# The UI will be available at http://localhost:3000

# Run tests (from repository root)
python tests/trust_fire_orchestrator.py
```

## Troubleshooting

### Common Issues

1. **`pf` command not found**: Make sure you've built the CLI and added it to your PATH
2. **`lake build` fails**: Ensure you're in the `spec-templates/v1/proofs` directory and have Lean 4 installed
3. **Python script errors**: Make sure you're running scripts from the repository root
4. **`deployment.yaml` not found**: The deployment files are Helm templates, not plain Kubernetes YAML. Use the inline examples from the README or set up Helm properly
5. **Kubernetes deployment fails**: Requires a running Kubernetes cluster (Docker Desktop, Minikube, or cloud cluster)
6. **Git Bash path issues**: Use forward slashes (`/`) instead of backslashes (`\`) in Git Bash
7. **Windows file removal issues**: Use the updated scripts with Windows-compatible file removal methods
8. **"Device or resource busy" errors**: Close any applications accessing the files and try again
9. **UI module resolution errors**: Ensure TypeScript configuration is properly set up in `marketplace/ui/tsconfig.json`
10. **Heroicons import errors**: Use the correct icon names (e.g., `CubeIcon` instead of `PackageIcon`, `ArrowDownTrayIcon` instead of `DownloadIcon`)

### Platform-Specific Notes

- **Windows**: Use `pf.exe` instead of `pf` and ensure proper PATH setup. **Use Windows Command Prompt instead of Git Bash for running installation scripts**
- **Git Bash/WSL**: Use `bash scripts/install.sh` for installation and forward slashes for paths
- **Lean 4**: May require network access for dependency downloads
- **Kubernetes**: Install Docker Desktop with Kubernetes enabled, or use Minikube for local development

### Windows Git Bash Path Issues

If you encounter path-related errors in Git Bash on Windows:

1. **Use forward slashes**: Always use `/` instead of `\` in paths
   ```bash
   # Correct
   bash scripts/install.sh
   cd core/cli/pf
   
   # Incorrect
   bash scripts\install.sh
   cd core\cli\pf
   ```

2. **File removal issues**: If you get "Device or resource busy" errors:
   - Close any file explorers or text editors accessing the files
   - Use the updated scripts which handle Windows file removal properly
   - Try running the script again after closing applications

3. **Command interpretation**: Git Bash interprets backslashes as escape characters:
   ```bash
   # Correct
   export PATH=$PATH:$(pwd)/core/cli/pf
   
   # Incorrect
   export PATH=$PATH:$(pwd)\core\cli\pf
   ```

4. **Troubleshooting**: If you're still having issues, run the troubleshooting script:
   ```bash
   bash scripts/windows-troubleshoot.sh
   ```

### Lean 4 Setup

For Lean 4 formal proofs:

1. **Install Lean 4**: Follow the [official installation guide](https://leanprover.github.io/lean4/doc/quickstart.html)
2. **Build proofs**: Run `cd spec-templates/v1/proofs && lake build`
3. **Network issues**: If you encounter certificate errors, try using a VPN or check your network settings

### Git Bash Specific Issues

If you're using Git Bash on Windows and encounter issues:

1. **Path separators**: Use forward slashes (`/`) instead of backslashes (`\`)
2. **Command execution**: Use `bash scripts/install.sh` instead of `scripts\install.bat`
3. **File permissions**: Some file operations may require different permissions in Git Bash
4. **Line endings**: Ensure files use Unix line endings (LF) instead of Windows line endings (CRLF)
5. **"Device or resource busy" errors**: Close any applications (file explorers, editors) that might be accessing the files
6. **File removal issues**: The scripts now use Windows-compatible file removal methods
7. **Backslash interpretation**: Git Bash interprets backslashes as escape characters, so always use forward slashes

### Known Issues

1. **Kubernetes Deployment**: The deployment files in `runtime/admission-controller/deploy/admission/templates/` are Helm templates and cannot be applied directly with `kubectl apply`. Use the inline deployment examples provided in the README or set up Helm properly.

2. **Chaos Test Output**: The chaos rollback test runs but may not produce visible output in some environments. This is expected behavior as the test simulates failure scenarios.

3. **Git Bash on Windows**: Installation scripts may have path and execution issues in Git Bash on Windows. **Use Windows Command Prompt instead of Git Bash for running installation scripts.**

4. **UI Development**: The React UI requires proper TypeScript configuration and may need dependency reinstallation if module resolution errors occur. The `tsconfig.json` file has been added to resolve these issues.

5. **Heroicons Library**: The UI uses Heroicons v2, which has different icon names than v1. The codebase has been updated to use the correct icon names.

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- [Lean 4](https://leanprover.github.io/) - Formal proof system
- [Marabou](https://github.com/NeuralNetworkVerification/Marabou) - Neural network verification
- [DryVR](https://github.com/verivital/dryvr) - Hybrid system verification
- [Sigstore](https://sigstore.dev/) - Cryptographic signing
- [Memurai](https://docs.memurai.com/) - Redis-compatible server for Windows

---

**Provability-Fabric** - Trust in AI through formal verification.
