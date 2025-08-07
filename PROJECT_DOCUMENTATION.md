# Provability-Fabric Project Documentation

## Project Overview

Provability-Fabric is an open-source framework that enforces provable behavioral guarantees through formal verification, runtime security mechanisms, and comprehensive audit trails.

## Architecture Components

### Core Components

1. **Specification Bundles** - YAML specifications with Lean proofs
2. **Runtime Guards** - Sidecar containers that monitor execution
3. **Solver Adapters** - Verification engines for neural networks and hybrid systems
4. **Marketplace UI** - React-based dashboard for package management and system monitoring

### Runtime Components

- **Sidecar Watcher** - Rust-based runtime monitor with plan validation and multi-channel input enforcement
- **Admission Controller** - Kubernetes webhook for validation
- **Transparency Ledger** - GraphQL service for audit trail
- **Incident Bot** - Automated incident response and rollback
- **WASM Sandbox** - Secure WebAssembly execution environment
- **Privacy Engine** - Epsilon-differential privacy enforcement
- **Marketplace API** - RESTful API for package management
- **Egress Firewall** - PII/secret detection with non-interference certificates

### Security Mechanisms

- **Plan-DSL & Policy Kernel** - Typed plans with capability validation
- **Capability Tokens** - DSSE-signed authorization tokens
- **Retrieval Gateway** - Tenant-isolated data access with receipts
- **Egress Firewall** - PII/secret detection and certificate generation with non-interference verdicts
- **System Invariants** - Formal Lean proofs of security properties
- **Evidence Artifacts** - DSSE-signed audit bundles
- **Test & SLO Harness** - Red-team testing and performance gates
- **Console Additions** - Security monitoring UI components
- **Zero-Retention** - TTL deletion and compliance attestation
- **Allow-list Generation** - Lean-to-JSON with CI drift detection
- **Documentation** - Guarantees, thresholds, and runbooks
- **Release Fences** - Mechanism validation gates
- **Multi-Channel Input Contract** - Trusted vs untrusted channel enforcement
- **Explicit SLO Thresholds** - Performance gates with per-component budgets
- **Accuracy Posture Evidence** - Evidence-linked responses with confidence tracking

## Production Features

### Security & Compliance

- **SLSA Level 3** - Supply chain security
- **SOC 2 Type II** - Compliance framework
- **Cross-Region DR** - Disaster recovery
- **RBAC** - Role-based access control
- **Network Policies** - Zero-trust networking
- **Formal Verification** - Lean proofs of security properties
- **Runtime Enforcement** - Sidecar-based security monitoring
- **Audit Trails** - Complete evidence generation and storage
- **Multi-Channel Security** - Trusted vs untrusted input enforcement
- **Non-Interference** - Formal guarantees in egress certificates

### Monitoring & Observability

- **Grafana Dashboards** - Real-time metrics with SLO panels
- **Prometheus** - Time-series monitoring
- **Jaeger** - Distributed tracing
- **Alertmanager** - Incident management
- **Security Console** - Plan validation, receipt viewing, certificate monitoring
- **Performance Gates** - SLO thresholds with per-component budgets

### CI/CD Pipeline

- **GitHub Actions** - Automated testing and deployment
- **Cross-Region Deployment** - Multi-region availability
- **Automated Rollbacks** - Incident response
- **Evidence Collection** - Compliance automation
- **Security Gates** - Mechanism validation in release pipeline
- **SLO Gates** - Performance validation in release pipeline

## Testing Framework

### Comprehensive Test Suite

```bash
# Run complete TRUST-FIRE suite
python tests/trust_fire_orchestrator.py

# Run comprehensive implementation tests
python test_all_components.py

# Test multi-channel input contract
python tests/redteam/injection_runner.py

# Test SLO performance gates
node tests/perf/latency_k6.js

# Run security mechanism tests
python tests/redteam/abac_fuzz.py --queries 1000
python tests/redteam/pii_leak.py --vectors 1000
```

### Test Results

- **26/27 tests passed** (96.3% success rate)
- **All core components verified**
- **Advanced security features tested**
- **Production-ready implementation**

## Documentation

### Core Documentation

- [Architecture Overview](docs/index.md)
- [Multi-Tenant Design](docs/multi-tenant.md)
- [Cross-Region DR](docs/cross-region-dr.md)
- [Compliance Framework](docs/compliance/)
- [Security Policies](docs/security/)
- [Operational Excellence](docs/playbooks/)

### Technical Documentation

- [Plan-DSL Specification](docs/spec/plan-dsl.md)
- [Runtime Attestation](docs/runtime/attestation.md)
- [Security Guarantees](docs/guarantees.md)
- [SLO Documentation](docs/runtime/slo.md)
- [Multi-Channel Input Contract](docs/spec/plan-dsl.md#multi-channel-input-contract)

## Development Setup

### Prerequisites

- **Go 1.21+** - For building CLI tools
- **Python 3.8+** - For running tests and scripts
- **Node.js 18+** - For UI components (optional)
- **Lean 4** - For formal proofs (optional)
- **kubectl** - For Kubernetes deployment (optional)
- **Rust** - For runtime components (optional)

### Installation

```bash
# Clone the repository
git clone https://github.com/fraware/provability-fabric.git
cd provability-fabric

# Build CLI tools from source
cd core/cli/pf && go build -o pf.exe . && cd ../..
cd cmd/specdoc && go build -o specdoc.exe . && cd ../..

# Install Python dependencies
if [ -f "tests/integration/requirements.txt" ]; then pip install -r tests/integration/requirements.txt; fi
if [ -f "tests/proof-fuzz/requirements.txt" ]; then pip install -r tests/proof-fuzz/requirements.txt; fi
if [ -f "tools/compliance/requirements.txt" ]; then pip install -r tools/compliance/requirements.txt; fi
if [ -f "tools/insure/requirements.txt" ]; then pip install -r tools/insure/requirements.txt; fi
if [ -f "tools/proofbot/requirements.txt" ]; then pip install -r tools/proofbot/requirements.txt; fi

# Install Node.js dependencies for UI components
cd marketplace/ui && npm install && cd ../..

# Run tests
python tests/trust_fire_orchestrator.py
```

## Troubleshooting

### Common Issues

1. **`pf` command not found**: Make sure you've built the CLI and added it to your PATH
2. **`lake build` fails**: Ensure you're in the `spec-templates/v1/proofs` directory and have Lean 4 installed
3. **Python script errors**: Make sure you're running scripts from the repository root
4. **Kubernetes deployment fails**: Requires a running Kubernetes cluster
5. **Git Bash path issues**: Use forward slashes (`/`) instead of backslashes (`\`) in Git Bash

### Platform-Specific Notes

- **Windows**: Use `pf.exe` instead of `pf` and ensure proper PATH setup
- **Git Bash/WSL**: Use `bash scripts/install.sh` for installation and forward slashes for paths
- **Lean 4**: May require network access for dependency downloads
- **Kubernetes**: Install Docker Desktop with Kubernetes enabled, or use Minikube for local development

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](LICENSE) file for details.

## Acknowledgments

- [Lean 4](https://leanprover.github.io/) - Formal proof system
- [Marabou](https://github.com/NeuralNetworkVerification/Marabou) - Neural network verification
- [DryVR](https://github.com/verivital/dryvr) - Hybrid system verification
- [Sigstore](https://sigstore.dev/) - Cryptographic signing
- [Memurai](https://docs.memurai.com/) - Redis-compatible server for Windows

---

**Provability-Fabric** - Trust in AI through formal verification and comprehensive security mechanisms with advanced multi-channel security and performance guarantees. 