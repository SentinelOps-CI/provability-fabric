# Reuse and Extend

This guide is for users who want to fork the repository, run a minimal subset, or extend Provability-Fabric with custom adapters and bundle templates without modifying core code.

## Modular layout (three tiers)

| Tier | Contents | Prerequisites |
|------|----------|---------------|
| **Minimal** | CLI (`core/cli/pf`), `spec-templates/v1`, `bundles/`, config schemas | Go 1.21+; Lean 4 optional for proofs |
| **Standard** | Minimal + Rust workspace (attestor, sidecar-watcher, adapters/http-get, adapters/file-read, etc.) + optional Go services | Go, Rust; Node/Docker optional |
| **Full** | All platform services, console, ledger, bench, experiments, demos | Go, Rust, Node, Python, Docker; see [Getting started](getting-started.md) |

Components not required for a minimal fork: `bench/`, `experiments/`, `console/`, `marketplace/`, `demos/`, and optional Rust crates (egress-firewall, core/sdk/rust, fuzz). See [Extension points](extension-points.md) for runtime and adapter boundaries.

## Forking the repository

### Clone and fork

- Clone: `git clone https://github.com/SentinelOps-CI/provability-fabric.git` (or your fork URL).
- To contribute back: fork on GitHub, add your fork as a remote, and open pull requests to the upstream repo. See [Contributing](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md) and [Governance](../community/governance.md).

### What to change when maintaining your own fork

- **Branding and URLs**: Update org/repo names and links in README, docs, and any hardcoded references (e.g. `SentinelOps-CI/provability-fabric`). Search for the project name and repository URL across the repo.
- **Configuration**: Set fork-friendly settings (org name, API base URLs, feature flags) in project config or environment. See [Configuration reference - Fork-friendly settings](../reference/configuration.md#fork-friendly-settings) and the root `.env.example` (or `config/env.example`) for typical variables.
- **Documentation**: If you ship a variant, update README and `docs/` to describe your setup and any custom adapters or templates.

## Minimal reuse (CLI and bundles only)

Use this path if you only need to author specification bundles and run the CLI (no Docker, Node, or Rust).

### Prerequisites

- **Go 1.21+** (required)
- **Lean 4** (optional; only if you build or modify proofs under `spec-templates/v1/proofs` or bundle `proofs/`)

### Build and run

```bash
# From repository root
cd core/cli/pf && go build -o pf . && cd ../../..
# Windows: output is pf.exe; add the directory to PATH

# Create a new agent bundle from the default template
./pf init my-agent
# Windows: pf.exe init my-agent

# Edit bundles/my-agent/spec.yaml and bundles/my-agent/proofs/ as needed

# Pack the bundle (no signing)
./pf bundle pack bundles/my-agent -o my-agent.tar.gz
```

No config file is required for CLI-only usage. Optional: use `~/.config/provability-fabric/config.yaml` or `./provability-fabric.yaml` for project-level settings; see [Configuration](../reference/configuration.md).

### Verify minimal install

Run:

```bash
./pf --version
./pf init test-agent
./pf bundle pack bundles/test-agent -o /tmp/test-agent.tar.gz
```

See also [scripts/test-new-user.sh](https://github.com/SentinelOps-CI/provability-fabric/blob/main/scripts/test-new-user.sh) (and `.bat` on Windows) with minimal mode.

## Standard reuse (CLI + Rust workspace)

Add the Rust runtime and adapters used in your deployment.

### Prerequisites

- Go 1.21+ and Rust (toolchain from root `rust-toolchain.toml`)
- Optionally Node and Docker if you run platform services

### Build

```bash
# CLI (as above)
cd core/cli/pf && go build -o pf . && cd ../../..

# Rust workspace (from repo root)
cargo build --workspace
```

Optional crates (egress-firewall, core/sdk/rust, etc.) need extra deps; see root [Cargo.toml](https://github.com/SentinelOps-CI/provability-fabric/blob/main/Cargo.toml). Build them separately when needed.

### Install script (standard mode)

- Linux/macOS: `./scripts/install.sh --standard` or `INSTALL_MODE=standard ./scripts/install.sh`
- Windows: `set INSTALL_MODE=standard` then `scripts\install.bat`

See [Install modes](#install-modes) below.

## Full install (all components)

For the complete platform (all Go services, console, ledger, bench tooling):

- Linux/macOS: `./scripts/install.sh` or `./scripts/install.sh --full`
- Windows: `scripts\install.bat` or `set INSTALL_MODE=full` then `scripts\install.bat`

See [Getting started](getting-started.md) and the root [README](https://github.com/SentinelOps-CI/provability-fabric/blob/main/README.md).

## Install modes

The install scripts support three modes:

| Mode | Flag / env | Behavior |
|------|------------|----------|
| **minimal** | `--minimal` or `INSTALL_MODE=minimal` | Build CLI only; create `bundles` dir; no Rust, Node, or optional Python |
| **standard** | `--standard` or `INSTALL_MODE=standard` | Build CLI + `cargo build --workspace`; no full Python/Node stacks |
| **full** | `--full` or `INSTALL_MODE=full` (default) | Current behavior: CLI, Rust, Python deps, Node where used |

Make targets: `make install-minimal`, `make install-standard`, `make install-full`. Default `make install` uses full.

## Adding adapters

Adapters live under `adapters/`. There are three kinds:

1. **Solver adapters** (e.g. Marabou, DryVR, alpha-beta-crown): invoked as scripts or CLIs; consume model + property, produce proof/artifact. Add a new directory under `adapters/` (e.g. `adapters/my-solver/`) with your script and any config; document how the platform invokes it (see [Extension points - Adapters](extension-points.md#adapters)).
2. **I/O adapters** (Rust: httpget, fileread): integrate with policy and resource mapping. Add a new crate under `adapters/` and, if needed, add it to the root Cargo workspace. See [Adapters overview](../adapters/overview.md).
3. **Middleware** (express, FastAPI, chi): integrate with your app stack. Add a new directory under `adapters/` (e.g. `adapters/my-middleware/`) and follow the same pattern as existing cert middleware.

Discovery is directory-based: add your adapter under `adapters/<name>` and reference it from specs or platform config. No dynamic plugin loader is required.

## Adding bundle templates

- **Default template**: `spec-templates/v1/` is copied by `pf init <agent-name>` into `bundles/<agent-name>/`. Layout: `spec.yaml`, `spec.md`, `taint.yaml`, `proofs/` (Lean toolchain, lakefile, Spec.lean).
- **Customizing the template**: Edit files in `spec-templates/v1/` to change the default content for new bundles. Keep the layout consistent (spec at top level, proofs in `proofs/`) so `pf bundle pack` and the platform continue to work.
- **Adding a second template (e.g. v2)**: Copy the entire `spec-templates/v1` directory to `spec-templates/v2`, adjust content, then either:
  - Use `pf init --template v2 my-agent` if the CLI supports a `--template` flag, or
  - Manually copy: `cp -r spec-templates/v2 bundles/my-agent` and rename/customize as needed.

Bundle manifest (policy_hash, automata_hash, labeler_hash) is defined by [bundle-manifest-v1.json](../schemas/bundle-manifest-v1.json). New bundles must stay consistent with that schema when integrating with the platform.

## Configuration

- **Full reference**: [Configuration](../reference/configuration.md) (hierarchy, file locations, API, database, verification, etc.).
- **Fork-friendly settings**: See [Configuration - Fork-friendly settings](../reference/configuration.md#fork-friendly-settings) and the root `.env.example` (or `config/env.example`) for variables commonly changed when forking (org name, base URLs, feature flags).

## Docker and platform services

The full web stack is optional. From the repo root:

- **Platform only** (postgres, redis, api-gateway, spec-service, proof-service, build-orchestrator, evidence-service, replay-service, runtime-sidecar): `docker compose up`
- **Full stack** (adds console, demos, Grafana, Prometheus): `docker compose --profile full up`

See root [README](https://github.com/SentinelOps-CI/provability-fabric/blob/main/README.md) and [docker-compose.yml](https://github.com/SentinelOps-CI/provability-fabric/blob/main/docker-compose.yml). For minimal or CLI-only use, no Docker is required.

## First-run verification

Scripts `scripts/test-new-user.sh` (Linux/macOS) and `scripts/test-new-user.bat` (Windows) verify an install. They respect install mode:

- **Minimal**: `pf --version`, `pf init test-agent`, optionally `pf bundle pack`.
- **Standard**: above plus `cargo test --workspace` (or subset).
- **Full**: full test suite as documented in [Contributing](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md).

Run them after install to confirm your tier works.
