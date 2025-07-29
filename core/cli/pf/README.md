# Provability-Fabric CLI (pf)

A command-line tool for managing AI agent specifications with provable behavioral guarantees through formal verification.

## Installation

```bash
go install github.com/provability-fabric/pf@latest
```

## Usage

### Initialize a new agent bundle

```bash
# Create a new agent specification bundle
pf init my-agent

# Preview what would be created
pf init my-agent --dry-run
```

### Lint specifications and proofs

```bash
# Run spectral linting and Lean builds
pf lint

# Preview linting operations
pf lint --dry-run
```

### Sign specification bundles

```bash
# Sign bundles with cosign
pf sign

# Sign specific bundle path
pf sign --path bundles/my-agent
```

### Check traceability

```bash
# Verify requirement-to-acceptance-criteria mappings
pf check-trace
```

## Examples

```bash
# Complete workflow for a new agent
pf init email-agent
cd bundles/email-agent
# Edit spec.yaml and proofs
pf lint
pf sign
```

## Development

```bash
# Build the CLI
go build -o pf main.go

# Run tests
go test ./...

# Install locally
go install .
```
