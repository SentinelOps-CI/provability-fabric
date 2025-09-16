# Standards-Only On-Ramp

The Standards-Only on-ramp focuses on emitting and verifying CERT-V1 standards without requiring the full Provability Fabric platform.

## Overview

This on-ramp provides:
- **CERT-V1 Standards**: Emit and verify compliance certificates
- **Minimal Integration**: Works with existing CI/CD pipelines
- **Zero Dependencies**: No sidecar or runtime components required
- **Quick Start**: Get started in minutes

## Quick Start

### 1. Install the CLI

```bash
# Install the so CLI
go install github.com/provability-fabric/core/cli/cmd/so@latest

# Verify installation
so --version
```

### 2. Create a Simple Policy

Create `policy.md`:

```markdown
# Security Policy

Allow authenticated users to access public APIs.
Forbid anonymous access to sensitive endpoints.
Rate limit API calls to 1000 per hour per user.
```

### 3. Compile and Verify

```bash
# Compile policy to ActionDSL
so policy compile --in policy.md --out build/

# Generate CERT-V1 certificate
so cert generate --policy build/action_dsl.json --out cert.json

# Verify certificate
so cert verify --cert cert.json
```

### 4. Integrate with CI

Add to your GitHub Actions:

```yaml
name: Standards Compliance
on: [push, pull_request]

jobs:
  standards:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install so CLI
        run: go install github.com/provability-fabric/core/cli/cmd/so@latest
        
      - name: Compile Policy
        run: so policy compile --in policy.md --out build/ --json
        
      - name: Generate Certificate
        run: so cert generate --policy build/action_dsl.json --out cert.json --json
        
      - name: Verify Certificate
        run: so cert verify --cert cert.json --json
```

## Features

### Policy Compilation
- English to ActionDSL conversion
- Real-time validation and warnings
- JSON output for CI integration

### Certificate Generation
- CERT-V1 compliant certificates
- Cryptographic signatures
- Metadata and provenance tracking

### Verification
- Certificate validation
- Signature verification
- Compliance checking

## Configuration

### Policy Format

Policies are written in natural English and support:

```markdown
# Allow/Forbid Rules
Allow role:admin to access sensitive_data
Forbid role:user to modify system_config

# Rate Limiting
Rate limit api_calls to 100 per minute
Limit database_queries to 50 per hour

# Budget Constraints
Budget limit 1000 USD per month
Maximum cost 100 USD per operation
```

### Certificate Schema

Generated certificates follow CERT-V1 specification:

```json
{
  "certificate_version": "CERT-V1",
  "policy_hash": "sha256:...",
  "timestamp": "2025-01-27T14:00:00Z",
  "issuer": "provability-fabric",
  "signature": "...",
  "metadata": {
    "policy_id": "security-policy",
    "version": "1.0.0"
  }
}
```

## Integration Examples

### Docker

```dockerfile
FROM golang:1.21-alpine AS builder
RUN go install github.com/provability-fabric/core/cli/cmd/so@latest

FROM alpine:latest
COPY --from=builder /go/bin/so /usr/local/bin/
COPY policy.md .
RUN so policy compile --in policy.md --out build/
```

### Kubernetes

```yaml
apiVersion: batch/v1
kind: Job
metadata:
  name: standards-compliance
spec:
  template:
    spec:
      containers:
      - name: so-cli
        image: provability-fabric/so:latest
        command: ["so", "policy", "compile", "--in", "policy.md", "--out", "/output"]
        volumeMounts:
        - name: policy
          mountPath: /policy.md
        - name: output
          mountPath: /output
      volumes:
      - name: policy
        configMap:
          name: security-policy
      - name: output
        emptyDir: {}
```

## Migration Path

From Standards-Only, teams can gradually adopt:

1. **Evidence + Replay**: Add TRACE-REPLAY-KIT for nightly builds
2. **Full Platform**: Implement sidecar integration with epochs and IFC

## Support

- Documentation: [docs/standards.md](../../docs/standards.md)
- Examples: [examples/standards-only/](../examples/)
- CLI Reference: [docs/cli-reference.md](../../docs/cli-reference.md)
