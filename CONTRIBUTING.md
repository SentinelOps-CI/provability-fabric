# Contributing to Provability-Fabric

Thank you for your interest in contributing. This document covers how to get started, run tests, and submit changes. For governance, RFC process, and voting, see the [Community Governance](docs/community/governance.md) guide.

## License and conduct

- This project is licensed under the [Apache License 2.0](LICENSE). By contributing, you agree that your contributions will be licensed under the same license.
- We expect respectful, inclusive, and constructive behavior. See [Community Governance - Code of Conduct](docs/community/governance.md) for guidelines.

For **security vulnerabilities**, use the process in [SECURITY.md](SECURITY.md) (private report; do not file a public issue first).

## How to contribute

1. **Fork** the repository and create a feature branch.
2. **Build and test** (see below) so your changes do not break the project.
3. **Document** any user-facing or config changes.
4. **Submit** a pull request with a clear description and reference to any related issues.

For the full pull request and review process, see [Governance - Pull Request Process](docs/community/governance.md).

## Building the project

### Minimal (CLI and bundles only)

If you only need the CLI and spec/bundle workflow (no Rust, Node, or Docker):

```bash
# Requires Go 1.23+ (see core/cli/pf/go.mod)
cd core/cli/pf && go build -o pf . && cd ../../..
# Add the binary to your PATH; on Windows the output is pf.exe
```

Optional: build the specdoc CLI if present:

```bash
[ -f cmd/specdoc/main.go ] && cd cmd/specdoc && go build -o specdoc . && cd ../..
```

### Standard (CLI + Rust workspace)

Build the CLI as above, then build the Rust workspace (requires [Rust](https://rustup.rs/) and `rust-toolchain.toml`):

```bash
cargo build --workspace
```

Optional crates (e.g. egress-firewall, core/sdk/rust) may need extra dependencies; see root [Cargo.toml](Cargo.toml) comments. Build them separately when needed.

### Full (all components)

Run the installation script for your platform:

- Linux/macOS: `./scripts/install.sh` (or `./scripts/install.sh --full` for full mode)
- Windows: `scripts\install.bat` (or with `INSTALL_MODE=full`)

See [Reuse and extend](docs/guides/reuse-and-extend.md) for install modes (minimal, standard, full) and tiered setup.

## Running tests

### Minimal checks

- **CLI version**: `./pf --version` (or `pf.exe --version` on Windows) from the repo root after building the CLI.
- **CLI unit tests**: From `core/cli/pf`, run `go test ./...`

### Standard (plus Rust)

From repo root:

```bash
cargo test --workspace --exclude sidecar-watcher
cargo test -p sidecar-watcher --lib
cargo test -p sidecar-watcher --tests
# Clippy (full workspace): cargo clippy --workspace -- -D warnings
```

`sidecar-watcher` uses `autotests = false` and explicit `[[test]]` entries for integration binaries that compile; other sources under `runtime/sidecar-watcher/tests/` are quarantined until updated (see `runtime/sidecar-watcher/tests/README.md`). CI runs `--lib` and `--tests` (see `.github/workflows/reusable-ci-rust.yml`).

### Full test suite

From repo root:

```bash
python tests/trust_fire_orchestrator.py
# Integration: python tests/integration/test_platform_integration.py
# See Makefile: make test
```

Install Python dependencies as needed (e.g. `pip install -r tests/integration/requirements.txt`). Minimal install does not need Python tooling; for full dev run `pip install -r requirements-optional.txt` (see root `requirements-optional.txt`).

## Reuse and forking

If you are forking the repo to build your own product or variant, see the [Reuse and extend](docs/guides/reuse-and-extend.md) guide. It covers:

- Minimal vs standard vs full setup
- What to rename or configure when forking (branding, URLs)
- Adding adapters and bundle templates
- Fork-friendly configuration

## Documentation

- [Getting started](docs/guides/getting-started.md)
- [Developer guide](docs/guides/developer-guide.md)
- [CI and supply-chain reference](docs/reference/ci-reference.md) (workflows, local commands, artifacts not to commit)
- [Extension points](docs/guides/extension-points.md) (adapters, bundles, runtime)
- [Configuration reference](docs/reference/configuration.md)

## Questions

- **GitHub Issues**: Bug reports and feature requests.
- **GitHub Discussions**: General questions and ideas.
- **Governance**: [Community Governance](docs/community/governance.md) for RFCs, working groups, and decision-making.
