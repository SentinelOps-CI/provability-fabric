# Provability Fabric On-Ramps

Three progressive adoption paths to accommodate varying team needs and requirements.

## Overview

Provability Fabric offers three distinct on-ramps that allow teams to adopt the platform incrementally, starting with basic compliance and gradually adding more sophisticated capabilities.

## On-Ramp Comparison

| Feature | Standards-Only | Evidence + Replay | Full Platform |
|---------|---------------|-------------------|---------------|
| **CERT-V1 Standards** | ✅ | ✅ | ✅ |
| **Policy Compilation** | ✅ | ✅ | ✅ |
| **Certificate Verification** | ✅ | ✅ | ✅ |
| **TRACE-REPLAY-KIT** | ❌ | ✅ | ✅ |
| **Nightly Builds** | ❌ | ✅ | ✅ |
| **Evidence Collection** | ❌ | ✅ | ✅ |
| **Sidecar Integration** | ❌ | ❌ | ✅ |
| **Epoch Management** | ❌ | ❌ | ✅ |
| **Information Flow Control** | ❌ | ❌ | ✅ |
| **Deterministic Egress** | ❌ | ❌ | ✅ |
| **MPC Fintech** | ❌ | ❌ | ✅ |
| **Privacy Controls** | ❌ | ❌ | ✅ |
| **RAG Guards** | ❌ | ❌ | ✅ |

## 1. Standards-Only On-Ramp

**Best for**: Teams wanting to start with basic compliance and standards verification.

### Key Features
- Emit and verify CERT-V1 standards
- English to ActionDSL policy compilation
- Certificate generation and validation
- CI/CD integration
- Zero runtime dependencies

### Use Cases
- Compliance reporting
- Policy documentation
- Basic audit trails
- Standards verification

### Getting Started
```bash
# Install CLI
go install github.com/provability-fabric/core/cli/cmd/so@latest

# Compile policy
so policy compile --in policy.md --out build/

# Generate certificate
so cert generate --policy build/action_dsl.json --out cert.json
```

[📖 Full Documentation →](./standards-only/)

## 2. Evidence + Replay On-Ramp

**Best for**: Teams needing deterministic verification and nightly validation.

### Key Features
- Everything from Standards-Only
- TRACE-REPLAY-KIT integration
- Nightly build validation
- Evidence collection and audit trails
- Low-view comparison and drift detection

### Use Cases
- Deterministic testing
- Regression detection
- Nightly validation pipelines
- Evidence-based compliance
- Audit trail generation

### Getting Started
```bash
# Set up nightly replay
so trace run --trace fixtures/trace.json --out replay-output/

# Compare with previous runs
so trace compare-lowview --in replay-output/ --threshold 0.999999

# Generate evidence report
so trace report --in replay-output/
```

[📖 Full Documentation →](./evidence-replay/)

## 3. Full Platform On-Ramp

**Best for**: Teams requiring comprehensive runtime enforcement and advanced capabilities.

### Key Features
- Everything from previous on-ramps
- Sidecar integration with runtime enforcement
- Epoch management for permission revocation
- Information Flow Control (IFC)
- Deterministic egress handling
- Advanced runtime components (MPC, privacy, RAG guards)

### Use Cases
- Production runtime enforcement
- Real-time policy enforcement
- Advanced security controls
- Multi-party computation
- Privacy-preserving operations
- RAG system protection

### Getting Started
```bash
# Deploy full platform
docker compose up -d --build

# Configure sidecar
so deploy --epoch stable --sidecar enabled

# Enable advanced features
so deploy --feature mpc-fintech --feature privacy --feature rag-guard
```

[📖 Full Documentation →](./full-platform/)

## Migration Paths

### From Standards-Only to Evidence + Replay

1. **Install TRACE-REPLAY-KIT**
   ```bash
   pip install -r external/TRACE-REPLAY-KIT/requirements.txt
   ```

2. **Create Trace Fixtures**
   ```bash
   # Create fixtures directory
   mkdir -p fixtures
   # Add trace files
   cp examples/traces/*.json fixtures/
   ```

3. **Set Up Nightly Builds**
   ```bash
   # Add to CI/CD pipeline
   so trace run --trace fixtures/trace.json --out replay-output/
   ```

### From Evidence + Replay to Full Platform

1. **Deploy Runtime Components**
   ```bash
   docker compose up -d --build
   ```

2. **Configure Sidecar Integration**
   ```bash
   so deploy --sidecar enabled --epoch stable
   ```

3. **Enable Advanced Features**
   ```bash
   so deploy --feature mpc-fintech --feature privacy
   ```

## Choosing the Right On-Ramp

### Start with Standards-Only if:
- You need basic compliance reporting
- You want to document policies in a structured way
- You're just getting started with formal verification
- You don't need runtime enforcement

### Upgrade to Evidence + Replay if:
- You need deterministic testing and validation
- You want to detect regressions automatically
- You need comprehensive audit trails
- You're building CI/CD pipelines with verification

### Choose Full Platform if:
- You need runtime policy enforcement
- You're running production workloads
- You need advanced security controls
- You want comprehensive platform capabilities

## Support and Resources

### Documentation
- [Standards-Only Guide](./standards-only/)
- [Evidence + Replay Guide](./evidence-replay/)
- [Full Platform Guide](./full-platform/)
- [CLI Reference](../../docs/reference/cli-reference.md)

### Examples
- [Standards-Only Examples](../examples/standards-only/)
- [Evidence + Replay Examples](../examples/evidence-replay/)
- [Full Platform Examples](../examples/full-platform/)

### Community
- [GitHub Discussions](https://github.com/SentinelOps-CI/provability-fabric/discussions)
- [Discord Community](https://discord.gg/provability-fabric)
- [Documentation Site](https://docs.provability-fabric.io)

## Getting Help

1. **Check Documentation**: Start with the relevant on-ramp guide
2. **Browse Examples**: Look at example configurations and use cases
3. **Join Community**: Ask questions in GitHub Discussions or Discord
4. **Open Issues**: Report bugs or request features on GitHub
5. **Professional Support**: Contact support@provability-fabric.io for enterprise needs
