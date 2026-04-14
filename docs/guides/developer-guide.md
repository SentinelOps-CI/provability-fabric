# Developer Guide

This guide provides comprehensive information for developers working with Provability-Fabric, including setup, development workflows, and contribution guidelines.

## Development Environment Setup

### Prerequisites

- **Go 1.23+** - Core services and CLI tools
- **Rust (stable)** - Performance-critical components; see root `rust-toolchain.toml`
- **Lean 4** - Formal proof development
- **Docker** - Container management
- **Kubernetes** - Local development cluster
- **Node.js 20+** - UI and TypeScript components

### Installation

```bash
# Clone the repository (upstream; use your fork URL if contributing)
git clone https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric

# Install Go dependencies (run from each Go module you use, e.g. core/cli/pf)
cd core/cli/pf && go mod download && cd ../../..

# Install Rust dependencies
cargo fetch

# Install Lean dependencies (from the Lake project you are building)
lake update

# Node.js: install per package (there is no root package.json). Examples:
#   cd runtime/ledger && npm ci && npx prisma generate && cd ../..
#   cd console && npm ci && cd ../..
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
├── bench/          # Benchmarks (SWE-bench: runner.py / RunConfig / _execute_run, runner_core.run_swebench, replay, cost accounting, atomic predictions, run_status.json, predictions.sha256, env.json, empty_patch_reason codes). Real agent runs and harness require WSL/Linux; smoke and unit tests use mock/fixtures and run on any OS.
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

- **`runtime/admission-controller/`** - Kubernetes admission controller (Go)
- **`runtime/attestor/`** - Attestation service (Rust; Redis-backed)
- **`runtime/kms-proxy/`** - KMS/key proxy for signing and encryption (Rust)
- **`runtime/tool-broker/`** - Tool approval and broker (Rust)
- **`runtime/sidecar-watcher/`** - Runtime monitoring and policy enforcement (Rust)
- **`runtime/labeler/`** - Proof-carrying labeler for JSON path and taint rules (Rust)
- **`runtime/wasm-sandbox/`** - WASM execution environment for adapters (Rust; wasmtime)
- **`runtime/ledger/`** - Transparency ledger (Node/TypeScript)

Rust runtime crates and the Rust adapters (`adapters/http-get`, `adapters/file-read`) are part of the root Cargo workspace. See **Rust workspace** below.

### Benchmarks (SWE-bench)

- **`bench/swebench/`** - SWE-bench runner and PF evidence pipeline. **Layout:** `run_config.py` (`RunConfig`, `build_argument_parser`), `runner.py` (`main()` → validated `RunConfig` → `_execute_run`), `runner_core.py` (`run_swebench(config)` for programmatic use), `workspace_manager.py`, `instance_processor.py`, `evidence_writer.py`, `predictions_writer.py`, `summary_writer.py`, `cost_reporter.py`, **`provider_env.py`** (shared OpenHands LLM provider, keys, Prime default base URL, `env.json` diagnostics), `engines/` (OpenHands, mock, `openhands_adapter.get_engine`, optional `deterministic_engine`). Run with `pf bench swebench run` (or `python bench/swebench/runner.py` from repo root). Use `--experiment-dir` to point at an experiment (e.g. `experiments/exp-step2-lite-smoke`); the runner then uses `manifest.json` budgets (`max_steps`, `timeout_sec`) as defaults. With `--engine openhands`, OpenHands must be available or the run exits (no stub). Produces `predictions.jsonl` (SWE-bench schema), `predictions.sha256` (same dir), `predictions.pfmeta.jsonl` (PF provenance sidecar, optional `empty_patch_reason`), and evidence under `runs/<run_id>/<instance_id>/` (run.log, model.patch, metadata.json, patch_apply_check.json with optional `empty_patch_reason`, empty_patch_reason.txt, engine_trace.json, replay_bundle.json, cost_report.json, **timing.json** with wall_clock_s, timeout_reached, termination_reason). When guarded: `evidence/` and `policy_compliance_summary.json` are always written. Runner writes `run_status.json` and `runs/<run_id>/env.json` (python_version, platform, pip_freeze_hash, openhands_version, datasets_version, swebench_version when available). Replay: `pf bench swebench replay --run_id <id>`. See `bench/swebench/README.md` for full options, **entry points** (pf CLI vs Python runner), **known limitations** (large repos, preflight caveat), **reproducibility** (env.json, env_drift, version pinning), and **engine tuning** (constants.py, PF_* env overrides). **Canonical Step-2 entrypoint:** `bash experiments/scripts/run-baseline-pf-cycle.sh` (optional `--update-run-ids`, `--triage`). **Golden cycle:** One trusted baseline+PF pair; see `experiments/exp-step2-lite-smoke/golden-cycle.md` for artifacts and acceptance checks; `run-ids.md` updated only via `update_run_ids_if_green.py`. **Makefile:** `make swebench-step2`, `make swebench-compare BASELINE_RUN_DIR=... PF_RUN_DIR=...`, `make swebench-triage`, `make swebench-regressions` (list_delta_cases + extract_case_bundle + bucket for baseline_solved_pf_failed slice). **Run/eval binding:** Harness writes `eval_metadata.json` per eval dir (run_id, predictions_sha256, dataset/split/versions). Compare with `--require-harness` enforces run_id consistency, predictions_sha256 when present, and **stale-eval check** (predictions file must not be newer than eval report). **Budget drift:** When both run dirs have `experiment_manifest.json`, compare asserts timeout_sec, max_steps, max_tool_calls, model, model_params match; drift fails the run. Compare report includes reproducibility fields, `empty_patch_reasons_topN`, **replay** (from replay_summary.json; run_replay_sample also writes **replay/instance_results.jsonl**; replays all when PF-resolved zero-violation count ≤20, else deterministic sample), **policy** (reason_codes_topN, denied_commands_topN), and **denial recovery** (denials_total_pf, episodes_aborted_after_denial_pf, recovered_after_denial_pf_rate); schema `experiments/schemas/compare_report.schema.json`. **Green run packaging:** When `update_run_ids_if_green.py` passes all gates, it runs export and writes `publish/PUBLISH.md`, **publish/GOLDEN.ok** (run IDs, pf_commit, timestamp, parity_gate_passed), **publish/RESULTS.md** (audit summary). `run-ids.md` is under **experiments/exp-step2-lite-smoke/run-ids.md**. **Stress slice:** `experiments/exp-step2-lite-stress-large-repos/`; `.github/workflows/bench-swebench-stress-scheduled.yaml` runs weekly and calls **`experiments/scripts/summarize_stress_run.py`** to produce **stress_summary.json** (timeout_rate_*, wall_clock_s median/p95, guard_overhead_s_median). **Expanded slices:** `experiments/exp-step2-lite-medium-50/`, `experiments/exp-step2-lite-fullish-200/`. **Criterion benchmarks:** `make bench-save-baseline` saves Criterion baseline and writes `bench/BASELINE.md` (date, git_sha, machine); CI has a smoke-bench job (compile + run, no regression gate). **Tests:** Smoke `pytest tests/test_swebench_runner_smoke.py -q`. Provider/compare/eval cleanup/regression bundle: see **`docs/internal/swebench-stabilization-regression-matrix.md`**. CI (`.github/workflows/bench-swebench-unit.yaml`) runs: test_experiments_compare_runs, test_validate_predictions, test_check_no_stub, test_validate_pf_run, test_loader_from_file, test_workspace_plan, test_replay_roundtrip, test_swebench_runner_smoke, test_openhands_engine, test_policy_loader, test_cost_report, test_proof_hook, test_check_wsl_env, test_fill_manifest_from_run, test_list_delta_cases, test_bucket_pf_failures, test_policy_guard_deny_allow, **test_provider_env**, **test_openhands_provider_env**, **test_run_swebench_eval_cleanup**, **test_run_config**. Additional in-repo tests (run locally as needed): test_runner_core, test_instance_processor, test_workspace_manager, test_evidence_writer, test_engine_interface, test_predictions_writer, test_summary_writer, test_runner_cost_reporter_facade, test_swebench_edge_cases, test_swebench_properties, test_error_recovery, test_summarize_stress_run. Real agent runs and harness require WSL or Linux.

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

### 3. Rust workspace

The repo root defines a Cargo workspace (see root `Cargo.toml` and `rust-toolchain.toml`). From the repo root:

- **Build:** `cargo build` (all workspace members)
- **Test:** `cargo test --workspace --exclude sidecar-watcher`, `cargo test -p sidecar-watcher --lib`, and `cargo test -p sidecar-watcher --tests` (explicit `[[test]]` targets; see `runtime/sidecar-watcher/tests/README.md`)
- **Clippy:** `cargo clippy --workspace -- -D warnings`
- **Policy / advisories:** Install [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) and run `cargo deny check` (configuration in repository root `deny.toml`). CI runs this via `.github/workflows/cargo-deny.yml` when manifests change.

Optional crates (not in workspace or need extra deps): `runtime/egress-firewall` (Hyperscan), `core/sdk/rust` (protoc), `runtime/sidecar-watcher/fuzz`. See root `Cargo.toml` comments; build them separately when their dependencies are available. See [Extension points](extension-points.md) for runtime and adapter boundaries.

### 4. CI and workflow changes

- Main pipeline: `.github/workflows/ci.yml` and reusable `reusable-ci-*.yml` files (see [CI reference](../reference/ci-reference.md)).
- Editing workflows triggers **actionlint** (`.github/workflows/actionlint.yml`), which runs a pinned `rhysd/actionlint` container locally equivalent to: `docker run --rm -v "$PWD:/workspace" -w /workspace rhysd/actionlint:1.7.12 -color`.

### 5. Rust code quality

- Prefer targeted `#[allow(dead_code)]` on specific types or impls rather than crate-level allows. Over time, remove unused code or implement stubs so allows can be narrowed or removed.
- Track TODOs in issues; use `// TODO(issue-N):` in comments when possible.

### 6. Building

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

### 7. Local Development

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
