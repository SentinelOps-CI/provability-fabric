# Getting started (first 15 minutes)

This is the shortest path from a clean clone to a running local stack. For contribution norms, see [CONTRIBUTING.md](../CONTRIBUTING.md). For the full launch matrix, see [dev/local-workflows.md](dev/local-workflows.md).

## What you get

Provability Fabric connects **specs and Lean proofs** (where present) to **runtime enforcement** and **auditable evidence**. Guarantees depend on configured trust roots and deployment policy — see [Evidence non-claims](roadmap/evidence-v0.2-status.md#explicit-non-claims).

## Prerequisites

| Tool | Notes |
|------|--------|
| Git | Clone with submodules when you need standards/replay |
| Go 1.23+ | CLI (`core/cli/pf`) |
| Rust (stable) | See root `rust-toolchain.toml` |
| Node.js 20+ | Ledger / console |
| Docker | Compose profiles for platform / ledger / full |
| Make | Primary task runner (`just` optional wrappers) |

Windows: prefer **WSL** for SWE-bench / replay harness paths. Native Windows works for CLI, many Rust tests, and Compose.

## Minute 0–5: clone and CLI

```bash
git clone --recurse-submodules https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric

# Optional: Go workspace for multi-module local edits
./scripts/go-work-init.sh          # or: make go-work
# Windows PowerShell: copy go.work.example go.work

# Path-aware deps from recent changes (or SCOPE=all for full bootstrap)
make install-dev

# Build the CLI
cd core/cli/pf && go build -o pf . && cd ../../..
./core/cli/pf/pf --help            # Windows: core\cli\pf\pf.exe
```

Standards submodules (CERT-V1 / TRACE-REPLAY-KIT) when you need Evidence smoke locally:

```bash
make dev-standards                 # needs STANDARDS_GITHUB_TOKEN if repos are private
```

## Minute 5–10: wiring and a warm stack

```bash
make check-wiring                  # compose ports ↔ code defaults
make platform-up                   # postgres, redis, API plane, sidecar
# or ledger GraphQL loop:
make ledger-up                     # + ledger on :4000
```

| URL | Service |
|-----|---------|
| http://localhost:8000 | API gateway (platform) |
| http://localhost:8006 | Sidecar / policy kernel |
| http://localhost:4000 | Ledger (ledger / full profiles) |
| http://localhost:3000 | Console (**full** profile only) |

Compose smoke without a long sleep:

```bash
make compose-smoke
```

Stop:

```bash
make down                          # or: docker compose down
```

## Minute 10–15: first useful checks

```bash
# Rust workspace smoke (optional; long)
cargo test -p sidecar-watcher --lib

# Ledger unit tests
cd runtime/ledger && npm test && cd ../..

# Docs site preview
pip install -r docs/requirements.txt
mkdocs serve                       # http://127.0.0.1:8000
```

## Where to go next

| Goal | Doc |
|------|-----|
| Day-to-day Make / Just matrix | [dev/local-workflows.md](dev/local-workflows.md) |
| Reuse CLI-only / fork minimal tree | [guides/reuse-and-extend.md](guides/reuse-and-extend.md) |
| Deploy with trust-chain env | [guides/deployment-guide.md](guides/deployment-guide.md) |
| Evidence + CERT formats | [evidence/overview.md](evidence/overview.md) |
| Architecture | [architecture/overview.md](architecture/overview.md) |
| CI / workflows | [reference/ci-reference.md](reference/ci-reference.md) |
| Maintainer remediation status | [internal/remediation-tracker.md](internal/remediation-tracker.md) |

## Honest defaults (Wave 9)

- **DSSE:** unset `PF_ENFORCE_DSSE` means **enforce** (fail-closed). Opt out only with `PF_ENFORCE_DSSE=0` or `false`. When enforcing, set `PF_TRUST_ROOT_PEM`.
- **Tenant / enabled tools:** deny-by-default patterns apply in production-shaped profiles; see deployment guide.
- **Lean in-repo ≠ every path proven.** Treat proofs as assets next to enforcement and evidence, not as a blanket warranty.
