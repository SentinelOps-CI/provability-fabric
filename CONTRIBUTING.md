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
git clone --recurse-submodules https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric
make dev-standards   # CERT-V1 + TRACE-REPLAY-KIT for evidence/replay tests
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

### Evidence and CI

Evidence changes should pass the [`evidence-v01-smoke.yml`](.github/workflows/evidence-v01-smoke.yml) workflow on Linux CI. Before opening a PR that touches `specs/evidence/**`, `core/evidence/**`, testbed scripts, or related tests:

```bash
make dev-standards   # CERT-V1 + TRACE-REPLAY-KIT submodules
make evidence-verify # Go tests, pytest suites, v0.1 + v0.2 testbed scripts
make docs-strict     # mkdocs build --strict (docs-only PRs)
```

`make evidence-verify` requires bash (Linux, WSL, or Git Bash on Windows). Clone external standards per [`external/README.md`](external/README.md).

#### `STANDARDS_GITHUB_TOKEN` (org admin)

CI workflows that call `make submodules` need a repository secret so GitHub Actions can clone private standards repos (`verifiable-ai-ci/CERT-V1`, `verifiable-ai-ci/TRACE-REPLAY-KIT`). **Org admin** must add the secret; contributors cannot self-serve it on the upstream org repo.

1. Create a fine-grained PAT (or classic PAT) owned by a bot/service account with **read** access to `verifiable-ai-ci/CERT-V1` and `verifiable-ai-ci/TRACE-REPLAY-KIT`.
2. In GitHub: **Settings → Secrets and variables → Actions → New repository secret**.
3. Name: `STANDARDS_GITHUB_TOKEN`, value: the PAT.
4. Verify locally (with the same token exported): `STANDARDS_GITHUB_TOKEN=<pat> make dev-standards`.
5. Verify in CI: re-run **Standards Pin Drift Check** or **Evidence v0.1 smoke** via `workflow_dispatch`; the `make submodules` step should succeed in the log.

Workflows using this secret are listed in [CI health matrix — Required secrets](docs/internal/ci-health-matrix.md#required-secrets-org-prerequisites). Forks without the secret can still run most gates; standards/replay jobs fail until the secret is configured or submodules are vendored locally.

See [Evidence v0.2 delivery guide](docs/roadmap/evidence-v0.2-delivery.md) for the fresh-clone checklist and [Evidence v0.2 status](docs/roadmap/evidence-v0.2-status.md) for current delivery gates.

### CI expectations

| Change type | Required local checks | CI workflows |
|-------------|----------------------|--------------|
| Evidence / standards | `make evidence-verify` | `evidence-v01-smoke.yml`, `standards-pin.yml` |
| Docs only | `make docs-strict` | `docs-build.yaml`, `docs-deploy.yaml` |
| Code (general) | `go test`, `cargo test`, targeted pytest | `ci.yml` reusable jobs |

Repo-wide triage and known failures: [CI health matrix](docs/internal/ci-health-matrix.md). Do not admin-merge while required checks are red (see **CI policy** below).

### CI policy

- **No admin merge on red:** merge only when all required status checks for the PR scope are green. Document any exception in the PR body and update the health matrix.
- **Local gates before CI PRs:** `make dev-standards`, `make evidence-verify` (evidence paths), `make docs-strict` (docs), `make proto-lint proto-validate` (protobuf).
- **Inventory:** run `scripts/ci_workflow_inventory.sh` on `main` after large workflow changes; see [CI health matrix](docs/internal/ci-health-matrix.md).

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
