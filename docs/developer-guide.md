# Developer Guide

This guide provides comprehensive information for developers working with Provability-Fabric, including setup, development workflows, and contribution guidelines.

## Development Environment Setup

### Prerequisites

- **Go 1.21+** - Core services and CLI tools
- **Rust 1.70+** - Performance-critical components
- **Lean 4** - Formal proof development
- **Docker** - Container management
- **Kubernetes** - Local development cluster
- **Node.js 18+** - UI and TypeScript components

### Installation

```bash
# Clone the repository
git clone https://github.com/provability-fabric/provability-fabric.git
cd provability-fabric

# Install Go dependencies
go mod download

# Install Rust dependencies
cargo fetch

# Install Lean dependencies
lake update

# Install Node.js dependencies
npm install
```

### Development Tools

```bash
# Install development tools
make install-dev-tools

# Verify installation
pf --version
lake --version
cargo --version
```

## Project Structure

```
provability-fabric/
├── core/           # Core framework components
├── runtime/        # Runtime services and components
├── adapters/       # Verification engine adapters
├── tests/          # Test suites and examples
├── docs/           # Documentation
├── tools/          # Development and build tools
└── scripts/        # Automation scripts
```

### Core Components

- **`core/cli/`** - Command-line interface
- **`core/sdk/`** - Client SDKs for multiple languages
- **`core/crypto/`** - Cryptographic utilities
- **`core/lean-libs/`** - Lean proof libraries

### Runtime Components

- **`runtime/admission-controller/`** - Kubernetes admission controller
- **`runtime/attestor/`** - Attestation service
- **`runtime/sidecar-watcher/`** - Runtime monitoring
- **`runtime/wasm-sandbox/`** - WASM execution environment

## Development Workflow

### 1. Feature Development

```bash
# Create feature branch
git checkout -b feature/your-feature-name

# Make changes and test
make test
make build

# Commit changes
git add .
git commit -m "feat: add your feature description"

# Push and create PR
git push origin feature/your-feature-name
```

### 2. Testing

```bash
# Run all tests
make test

# Run specific test suites
make test-unit
make test-integration
make test-e2e

# Run tests with coverage
make test-coverage

# Run performance benchmarks
make bench
```

### 3. Building

```bash
# Build all components
make build

# Build specific components
make build-core
make build-runtime
make build-adapters

# Build for different platforms
make build-multiarch
```

### 4. Local Development

```bash
# Start local development cluster
make dev-cluster

# Deploy to local cluster
make dev-deploy

# Monitor local deployment
make dev-monitor

# Clean up local environment
make dev-cleanup
```

## Lean Proof Development

### Setting Up Lean Environment

```bash
# Install Lean 4
curl -sL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Install mathlib
lake update

# Build Lean libraries
lake build
```

### Writing Proofs

```lean
import Mathlib.Data.String.Basic

-- Define your theorem
theorem example_theorem (x : Nat) : x + 0 = x := by
  -- Your proof here
  rw [Nat.add_zero]

-- Use Lean tactics
theorem another_theorem (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b
```

### Proof Quality Gates

```bash
# Check proof quality
make lean-gate

# Check build time budgets
make lean-time-budget

# Run proofbench
make proofbench
```

## Go Development

### Code Style

- Follow Go standard formatting (`gofmt`)
- Use `golint` for code quality
- Write comprehensive tests
- Use meaningful variable names

### Testing

```go
package core

import (
    "testing"
    "github.com/stretchr/testify/assert"
)

func TestExample(t *testing.T) {
    result := ExampleFunction()
    assert.Equal(t, expected, result)
}
```

### Building

```bash
# Build Go binaries
go build ./cmd/...

# Cross-compile
GOOS=linux GOARCH=amd64 go build ./cmd/...

# Install locally
go install ./cmd/...
```

## Rust Development

### Code Style

- Follow Rust formatting (`rustfmt`)
- Use `clippy` for linting
- Write comprehensive tests
- Use proper error handling

### Testing

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example() {
        let result = example_function();
        assert_eq!(result, expected);
    }
}
```

### Building

```bash
# Build Rust components
cargo build

# Build with optimizations
cargo build --release

# Run tests
cargo test

# Run benchmarks
cargo bench
```

## TypeScript/Node.js Development

### Code Style

- Use ESLint and Prettier
- Follow TypeScript best practices
- Write comprehensive tests
- Use proper type definitions

### Testing

```typescript
import { describe, it, expect } from 'vitest';
import { exampleFunction } from './example';

describe('exampleFunction', () => {
  it('should return expected result', () => {
    const result = exampleFunction();
    expect(result).toBe(expected);
  });
});
```

### Building

```bash
# Install dependencies
npm install

# Build TypeScript
npm run build

# Run tests
npm test

# Run linting
npm run lint
```

## Debugging and Troubleshooting

### Common Issues

1. **Lean Build Failures**
   ```bash
   # Check Lean version
   lean --version
   
   # Clean and rebuild
   lake clean
   lake build
   ```

2. **Go Module Issues**
   ```bash
   # Clean module cache
   go clean -modcache
   
   # Download dependencies
   go mod download
   ```

3. **Rust Compilation Errors**
   ```bash
   # Check Rust version
   rustc --version
   
   # Update Rust
   rustup update
   ```

### Debug Tools

```bash
# Enable debug logging
export PF_LOG_LEVEL=debug

# Run with debug flags
pf --debug

# Enable Go debug
export GODEBUG=1

# Enable Rust debug
RUST_LOG=debug cargo run
```

## Performance Optimization

### Profiling

```bash
# Go profiling
go test -cpuprofile=cpu.prof -memprofile=mem.prof

# Rust profiling
cargo install flamegraph
cargo flamegraph

# Lean profiling
lake build --profile
```

### Benchmarking

```bash
# Run all benchmarks
make bench

# Run specific benchmarks
cargo bench --package core
go test -bench=. ./core/...
```

## Contributing Guidelines

### Code Review Process

1. **Create Feature Branch** - Use descriptive branch names
2. **Write Tests** - Include tests for new functionality
3. **Update Documentation** - Keep docs current with code changes
4. **Submit PR** - Include clear description and testing notes
5. **Address Feedback** - Respond to review comments promptly

### Commit Messages

Use conventional commit format:

```
feat: add new feature
fix: resolve bug
docs: update documentation
style: format code
refactor: restructure code
test: add tests
chore: maintenance tasks
```

### Pull Request Checklist

- [ ] Tests pass locally
- [ ] Code follows style guidelines
- [ ] Documentation is updated
- [ ] Changes are tested
- [ ] No breaking changes (or documented)
- [ ] Commit messages are clear

## Getting Help

### Resources

- **Documentation**: This guide and other docs
- **GitHub Issues**: Bug reports and feature requests
- **Discord**: Community discussions and help
- **Code Examples**: Check the `examples/` directory

### Support Channels

- **Development Questions**: GitHub Discussions
- **Bug Reports**: GitHub Issues
- **Feature Requests**: GitHub Issues with enhancement label
- **Security Issues**: GitHub Security Advisories

## Conclusion

This guide provides the foundation for developing with Provability-Fabric. As you become more familiar with the framework, explore the codebase, contribute improvements, and help build a robust ecosystem for provable AI systems.

Remember to:
- Write clear, maintainable code
- Include comprehensive tests
- Update documentation
- Follow established patterns
- Contribute to the community
