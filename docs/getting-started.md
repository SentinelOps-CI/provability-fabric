# Getting Started with Provability-Fabric

Provability-Fabric is an open-source framework that binds every AI agent container image to a machine-checkable Lean proof (Proof-of-Behaviour), ensuring provable behavioral guarantees through formal verification.

## What is Provability-Fabric?

Provability-Fabric provides a comprehensive toolkit for creating AI agents with mathematically verifiable behavior. The framework combines specification-driven development with runtime enforcement to ensure agents operate within defined constraints. By binding container images to formal proofs, Provability-Fabric enables trust in AI systems through cryptographic verification rather than blind faith.

## Core Components

The framework consists of three core components:

1. **Specification Bundles** - Define agent behavior in YAML and Lean
2. **Runtime Guards** - Monitor execution in real-time
3. **Solver Adapters** - Verify neural network properties

This creates a complete pipeline from formal specification to deployed, verified agents.

## Key Features

- **Automatic Sidecar Injection** - Runtime monitoring without code changes
- **Admission Controllers** - Validate proofs before deployment
- **Transparency Ledger** - Immutable record of specifications and verification status
- **Multiple Verification Engines** - Support for Marabou (neural networks) and DryVR (hybrid systems)
- **Production Ready** - Comprehensive CI/CD integration, security policies, and community governance

## Quick Start

### Prerequisites

- Docker and Kubernetes
- Lean 4 (for proof development)
- Go 1.21+ (for core services)
- Rust 1.70+ (for performance components)

### Installation

```bash
# Clone the repository
git clone https://github.com/provability-fabric/provability-fabric.git
cd provability-fabric

# Install dependencies
make install

# Verify installation
pf --version
```

### Core Services

```bash
# Initialize a new agent specification
pf init my-agent

# Create and verify proofs
lake build

# Deploy with runtime monitoring
kubectl apply -f deployment.yaml
```

### Client SDKs

```bash
# TypeScript/Node.js
npm install @provability-fabric/core-sdk-typescript

# Go
go get github.com/provability-fabric/core/sdk/go

# Rust
cargo add provability-fabric-core-sdk-rust
```

### Performance Testing

```bash
# Run performance benchmarks
cargo bench

# WASM worker pool testing
cargo test --package wasm-sandbox

# Batch signature verification
cargo test --package crypto
```

## Your First Agent

### 1. Create Agent Specification

```bash
pf init my-first-agent
cd my-first-agent
```

### 2. Define Behavior

Edit `spec.yaml`:

```yaml
name: my-first-agent
version: 1.0.0
description: A simple AI agent with provable behavior

capabilities:
  - name: text_generation
    description: Generate text responses
    constraints:
      max_length: 1000
      content_filter: true

proofs:
  - name: behavior_verification
    type: lean
    file: proofs/behavior.lean
```

### 3. Write Lean Proofs

Create `proofs/behavior.lean`:

```lean
import Mathlib.Data.String.Basic

def max_response_length : Nat := 1000

theorem response_length_bound (response : String) : 
  response.length ≤ max_response_length := by
  -- Your proof here
  sorry
```

### 4. Build and Verify

```bash
# Build proofs
lake build

# Verify specification
pf verify

# Create deployment bundle
pf bundle
```

### 5. Deploy

```bash
# Apply to cluster
kubectl apply -f deployment.yaml

# Monitor runtime behavior
pf monitor my-first-agent
```

## Next Steps

- Read the [Architecture Overview](architecture.md) to understand system design
- Explore [Core Concepts](core-concepts.md) for detailed explanations
- Check [Examples](examples.md) for practical use cases
- Review [Security Overview](security/overview.md) for best practices

## Getting Help

- **Documentation**: Browse this documentation site
- **GitHub Issues**: Report bugs and request features
- **Discord**: Join our community for discussions
- **Examples**: Check the `examples/` directory for working code

## License

Apache 2.0 License - see [LICENSE](../LICENSE) for details.
