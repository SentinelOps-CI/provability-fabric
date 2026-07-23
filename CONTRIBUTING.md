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

#### Go workspace (local dev)

The repo has many `go.mod` files. For local multi-module work, **initialize a Go workspace** from the template (preferred over treating each module as an island):

```bash
./scripts/go-work-init.sh          # copies go.work.example -> go.work (gitignored)
# or: make go-work
./scripts/go-work-init.sh --sync   # optional: align sums after module changes
```

Equivalent manual step:

```bash
cp go.work.example go.work   # go.work is gitignored for local overrides
go work sync                 # optional
```

Primary CLI entrypoint remains `core/cli/pf`; `go.work` wires replace paths across modules without manual `replace` edits in each module.

For path-aware local deps (Go/Node/Python/Rust only where needed):

```bash
make install-dev                 # auto-detect from git changes
make install-dev SCOPE=node      # ledger/SDK/dsse-ts npm installs
make install-dev SCOPE=all       # full bootstrap (same as install-full)
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

## Local Docker / ledger loops

Prefer profile-scoped Make targets (health-wait, no fixed sleep). Full matrix: [docs/dev/local-workflows.md](docs/dev/local-workflows.md).

```bash
make platform-up     # default profile: platform + sidecar (:8000 / :8006)
make ledger-up       # + ledger GraphQL (:4000), PROFILE=dev
make check-wiring    # compose â†” code port defaults
# Console UI (:3000) requires: make full-up
```

`make dev` is an alias for `platform-up` and does **not** start the Console.

## Running tests

### Windows development (WSL-first)

**Primary path:** develop inside [WSL2](https://learn.microsoft.com/en-us/windows/wsl/install) (Ubuntu recommended). Clone the repo on the Linux filesystem (`~/provability-fabric`), and run bash/`make` targets from WSL. Linux CI remains authoritative for Lean/Lake, evidence replay, and full integration.

Native Windows (PowerShell/cmd) is an **optional smoke subset only** â€” do not chase native Lean, OpenHands, or full `make test` parity on Windows.

| Task | Windows native | WSL / Linux |
|------|----------------|-------------|
| Go CLI (`core/cli/pf`) | Pass â€” `go test ./...` | Pass |
| Rust workspace (non-excluded crates) | Pass (see smoke below) | Pass |
| Evidence validate/pack (`pf evidence`) | Pass (static paths) | Pass |
| Evidence replay execute, bash testbeds | **Skip** â€” needs bash + submodules | Pass |
| `make evidence-verify`, `make test` | **Use WSL** (Git Bash is partial) | Pass |
| SWE-bench real engine (OpenHands) | **Skip** | Pass |
| Lean / Lake builds | **Use WSL** â€” no native Lean in CI | Pass |
| Full platform docker compose | Partial | Pass |

**WSL setup (recommended):**

1. Install WSL2 + Ubuntu; enable Docker Desktop WSL integration if you use Docker.
2. Clone into `~/provability-fabric` (not under `/mnt/c/...`) for filesystem performance.
3. Run `make dev-standards`, then `make evidence-verify` / `make test` from WSL.

Git Bash can cover light gates (`make evidence-verify` subset) but not Lean/Lake or full integration tests.

Optional native Windows smoke (no WSL, no Lean):

```powershell
cd core\cli\pf; go test ./...
cargo test --workspace --exclude provability-fabric-core-sdk-rust --exclude sidecar-watcher --exclude labeler --exclude tool-broker
```

Same subset via Makefile (from Git Bash/WSL/`make` on Windows):

```bash
make test-windows   # CLI + Rust smoke; skips Linux-only paths
```

CI: optional path-filtered job `.github/workflows/test-windows.yml` runs that same subset on `windows-latest` (no Lean toolchain).

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
2. In GitHub: **Settings â†’ Secrets and variables â†’ Actions â†’ New repository secret**.
3. Name: `STANDARDS_GITHUB_TOKEN`, value: the PAT.
4. Verify locally (with the same token exported): `STANDARDS_GITHUB_TOKEN=<pat> make dev-standards`.
5. Verify in CI: re-run **Standards Pin Drift Check** or **Evidence v0.1 smoke** via `workflow_dispatch`; the `make submodules` step should succeed in the log.

Workflows using this secret are listed in [CI health matrix â€” Required secrets](docs/internal/ci-health-matrix.md#required-secrets-org-prerequisites). Forks without the secret can still run most gates; standards/replay jobs fail until the secret is configured or submodules are vendored locally.

See [Evidence v0.2 delivery guide](docs/roadmap/evidence-v0.2-delivery.md) for the fresh-clone checklist and [Evidence program closure](docs/roadmap/evidence-program-closure.md) for live gated CI posture (historical v0.2 status is archived).

### CI expectations

| Change type | Required local checks | CI workflows |
|-------------|----------------------|--------------|
| Evidence / standards | `make evidence-verify` | `evidence-v01-smoke.yml`, `standards-pin.yml` |
| Docs only | `make docs-strict` | `docs-build.yaml`, `docs-deploy.yaml` |
| Code (general) | `go test`, `cargo test`, targeted pytest | `ci.yml` reusable jobs |

Repo-wide triage: [remediation tracker](docs/internal/remediation-tracker.md); secrets stub: [CI health matrix](docs/internal/ci-health-matrix.md). Do not admin-merge while required checks are red (see **CI policy** below).

### CI policy

- **No admin merge on red:** merge only when all required status checks for the PR scope are green. Document any exception in the PR body and update the health matrix. Branch protection on `main` enforces **CI required checks**, **smoke**, **evidence-schema-only**, and **Documentation Build** (applied 2026-06-16).
- **Local gates before CI PRs:** `make dev-standards`, `make evidence-verify` (evidence paths), `make docs-strict` (docs), `make proto-lint proto-validate` (protobuf).
- **Inventory:** run `scripts/ci_workflow_inventory.sh` (Linux/macOS/WSL) or `scripts/ci_workflow_inventory.ps1` (Windows) on `main` after large workflow changes; see [CI health matrix](docs/internal/ci-health-matrix.md).

### Local pre-commit gates (Wave 0 / F36)

Install [pre-commit](https://pre-commit.com/) and enable hooks once per clone:

```bash
pip install pre-commit
pre-commit install
pre-commit run --all-files   # optional full sweep
```

Hooks mirror critical CI checks: `actionlint` on workflow files, placeholder scan (`scripts/check_no_placeholder.py`), trailing-whitespace/YAML hygiene, `gofmt`, and `cargo fmt`. See [.pre-commit-config.yaml](.pre-commit-config.yaml). On Windows without bash, run `pwsh scripts/ci_workflow_inventory.ps1` and targeted pytest/jest commands before opening a PR.

## Reuse and forking

If you are forking the repo to build your own product or variant, see the [Reuse and extend](docs/guides/reuse-and-extend.md) guide. It covers:

- Minimal vs standard vs full setup
- What to rename or configure when forking (branding, URLs)
- Adding adapters and bundle templates
- Fork-friendly configuration

## Documentation

- [Getting started](docs/getting-started.md)
- [Developer guide](docs/guides/developer-guide.md)
- [CI and supply-chain reference](docs/reference/ci-reference.md) (workflows, local commands, artifacts not to commit)
- [Extension points](docs/guides/extension-points.md) (adapters, bundles, runtime)
- [Configuration reference](docs/reference/configuration.md)

## Questions

- **GitHub Issues**: Bug reports and feature requests.
- **GitHub Discussions**: General questions and ideas.
- **Governance**: [Community Governance](docs/community/governance.md) for RFCs, working groups, and decision-making.
