> **Canonical first-15-minutes path:** [docs/getting-started.md](../getting-started.md) (CLI, wiring, Compose). This page adds product concepts and a longer first-agent walkthrough.

# Getting Started with Provability-Fabric

Provability-Fabric is an open-source framework that binds every AI agent container image to a machine-checkable Lean proof (Proof-of-Behaviour), ensuring provable behavioral guarantees through formal verification.

## What is Provability-Fabric?

Provability-Fabric provides a comprehensive toolkit for creating AI agents with mathematically verifiable behavior. The framework combines specification-driven development with runtime enforcement to ensure agents operate within defined constraints. By binding container images to formal proofs, Provability-Fabric grounds trust in AI systems on cryptographic verification and checkable claims.

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
- **Multiple Verification Engines** - Support for Marabou (neural networks), DryVR (hybrid systems), and Î±-Î²-CROWN (GPU-accelerated neural networks)
- **Production Ready** - Comprehensive CI/CD integration, security policies, and community governance

## Quick Start

### Prerequisites

- Docker and Kubernetes
- Lean 4 (for proof development)
- Go 1.23+ (for core services)
- Rust (stable; see root `rust-toolchain.toml`)
- Node.js 20+ (for UI and ledger)

For **SWE-bench agent runs and harness evaluation**: real runs and the SWE-bench harness require **WSL or Linux** (OpenHands uses `fcntl`; the harness uses `resource`). On native Windows, only `--engine mock` or `--mode deterministic` are allowed. See `experiments/exp-step2-lite-smoke/env-checklist.md` and `bench/swebench/README.md`. For the canonical experiment pipeline (replay sample, compare, green-run export and PUBLISH.md), see `experiments/README.md` and `experiments/exp-step2-lite-smoke/golden-cycle.md`.

For **minimal (CLI + bundles only)** or **standard (CLI + Rust)** setup without the full stack, see [Reuse and extend](reuse-and-extend.md).

### Installation

```bash
# Clone the repository (upstream; use your fork when contributing)
git clone https://github.com/SentinelOps-CI/provability-fabric.git
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
  response.length â‰¤ max_response_length := by
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

- Read the [Architecture Overview](../architecture/overview.md) to understand system design
- Check [Examples](examples.md) for practical use cases
- Review [Security Overview](../security/overview.md) for best practices

## Getting Help

- **Documentation**: Browse this documentation site
- **GitHub Issues**: Report bugs and request features
- **Discord**: Join our community for discussions
- **Examples**: Check the `examples/` directory for working code

## Proof-Carrying Science (optional)

When your work involves **science claim bundles** for lab QC release, tool-use safety, or reproducible computation, follow the dedicated PCS guides in order. Clone [pcs-core](https://github.com/SentinelOps-CI/pcs-core) beside this repository and set `PCS_CORE_PATH`, run `make demo-pcs` from the repository root, then read [PCS documentation](../pcs/README.md) for release mode and benchmarks together with the [release checklist](../pcs/release-checklist.md).

## License

Apache 2.0 License - see [LICENSE](../LICENSE) for details.

## Telemetry (Anonymous, Opt-In)

The console and CLI support anonymous, opt-in telemetry to help improve Developer Experience (DX).

- What is collected: minimal event types and timestamps for â€œinit â†’ first valid certâ€ and â€œfirst replay successâ€. No PII is collected; payloads are scrubbed server-side.
- Opt-in: Disabled by default unless `TELEMETRY_DEFAULT_ENABLED=true` is set on the API gateway. Users can enable/disable in the Console under Settings â†’ Anonymous usage telemetry.
- Disable:
  - Console: Settings â†’ toggle off â€œAnonymous usage telemetryâ€.
  - Environment: unset `TELEMETRY_DEFAULT_ENABLED` or set `TELEMETRY_DEFAULT_ENABLED=false` on the API gateway service.

See also: [Configuration](../reference/configuration.md) for environment variables.
