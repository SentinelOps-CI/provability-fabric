# Provability-Fabric Documentation

This directory contains the documentation for the Provability-Fabric framework. It is organized by audience and topic.

## Structure

| Section | Purpose |
|--------|---------|
| **guides/** | How-to guides: getting started, deployment, development, testing, examples, platform |
| **architecture/** | System design: overview, decision path, guarantees, policy, multi-tenant, cross-region DR |
| **reference/** | Technical reference: CLI, API, configuration, versioning, CI, errors, proof quality |
| **specs/** | Formal specifications: Plan DSL, egress certificate, DSSE verify contract, standards |
| **evidence/** | Evidence and CERTs: overview, replay |
| **security/** | Security: overview, threat model, SLSA, signing & rotation, enclave attestation |
| **runtime/** | Runtime: attestation, performance, SLOs |
| **adapters/** | Adapters: overview, alpha-beta-CROWN, action DSL sidecar |
| **pcs/** | Proof-Carrying Science: verify, sign, release chain, admission benchmarks |
| **integrations/** | Integrations: OpenAI, MCP (integration, quick reference, migration) |
| **runbooks/** | Operations: deployment, rollback, incident response, break glass, surge, approvals, GuardTrip triage |
| **features/** | Feature docs: real-time communication, dev mode, authentication, advanced search |
| **compliance/** | Compliance: SOC2, safety case, insurance |
| **community/** | Community: governance |
| **dev/** | Developer tooling: Lean build |
| **internal/** | Contributor tracking: placeholders inventory, burn-down, decisions, audit, solve-rate debugging, SWE-bench stabilization regression matrix |

**Bench (SWE-bench)** is documented primarily in the repository at `bench/swebench/README.md` and `experiments/README.md` (manifests, compare, publish). The MkDocs site links to those paths via the docs index; there is no separate `docs/bench/` tree.

## Entry points

- **[index.md](index.md)** - Documentation home and quick links
- **[guides/getting-started.md](guides/getting-started.md)** - Quick start and basic concepts
- **[architecture/overview.md](architecture/overview.md)** - System architecture
- **[evidence/overview.md](evidence/overview.md)** - Evidence and CERTs (see also [specs/standards.md](specs/standards.md), [evidence/replay.md](evidence/replay.md))
- **[pcs/README.md](pcs/README.md)** - Proof-Carrying Science: quickstart, verification, benchmarks, fixtures

## Building

The documentation site is built from the **repository root** using the root `mkdocs.yml` (output directory **`build/`**, not `site/`). Install Python dependencies first:

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Open `http://127.0.0.1:8000` to preview. For a static build: `mkdocs build` (writes `./build`). CI uses the same layout; see `.github/workflows/docs-build.yaml` and `.github/workflows/docs-deploy.yaml`.

The nested `docs/mkdocs.yml` is retained for alternate or partial builds; prefer the root config for the full site.

## Contributing

- Follow the structure and naming above; use clear language without emojis
- Keep docs in sync with code; use proper Markdown and fix links when moving files
- When you change GitHub Actions, the **actionlint** workflow (see [reference/ci-reference.md](reference/ci-reference.md)) validates workflow YAML; Rust dependency policy is enforced by **cargo-deny** and root `deny.toml`
