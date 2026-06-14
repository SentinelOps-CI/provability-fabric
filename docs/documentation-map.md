# Provability-Fabric Documentation

This directory contains the documentation for the Provability-Fabric framework, organized by audience and topic.

## Structure

| Section | Purpose |
|--------|---------|
| **guides/** | How-to guides for getting started, deployment, development, testing, examples, and platform topics |
| **architecture/** | System design including overview, decision path, guarantees, policy, multi-tenant, and cross-region DR |
| **reference/** | Technical reference for CLI, API, configuration, versioning, CI, errors, and proof quality |
| **specs/** | Formal specifications for Plan DSL, egress certificate, DSSE verify contract, and standards |
| **evidence/** | Evidence and CERTs with overview and replay guides |
| **security/** | Security overview, threat model, SLSA, signing and rotation, enclave attestation |
| **runtime/** | Runtime attestation, performance, and SLOs |
| **adapters/** | Adapter overview, alpha-beta-CROWN, and action DSL sidecar |
| **pcs/** | Proof-Carrying Science guides for verify, sign, release chain, and admission benchmarks |
| **integrations/** | OpenAI and MCP integration, quick reference, and migration |
| **runbooks/** | Operations for deployment, rollback, incident response, break glass, surge, approvals, GuardTrip triage |
| **features/** | Real-time communication, dev mode, authentication, advanced search |
| **compliance/** | SOC2, safety case, insurance |
| **community/** | Governance |
| **dev/** | Lean build tooling |
| **internal/** | Contributor-only notes excluded from published MkDocs nav; see [internal/README.md](internal/README.md) |
| **releases/** | Historical release notes including PCS RC archives |

**Bench (SWE-bench)** documentation lives primarily at `bench/swebench/README.md` and `experiments/README.md` for manifests, compare, and publish workflows. The MkDocs site links to those paths through the docs index; there is no separate `docs/bench/` tree.

## Entry points

- **[index.md](index.md)** — Documentation home and quick links
- **[guides/getting-started.md](guides/getting-started.md)** — Quick start and basic concepts
- **[architecture/overview.md](architecture/overview.md)** — System architecture
- **[evidence/overview.md](evidence/overview.md)** — Evidence and CERTs (see also [specs/standards.md](specs/standards.md) and [evidence/replay.md](evidence/replay.md))
- **[pcs/README.md](pcs/README.md)** — Proof-Carrying Science quickstart, verification, benchmarks, and fixtures

## Building

The documentation site builds from the **repository root** using the root `mkdocs.yml`. Output goes to **`build/`**. Install Python dependencies first.

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Open `http://127.0.0.1:8000` to preview. A static build with `mkdocs build` writes `./build/`. CI uses the same layout; see `.github/workflows/docs-build.yaml` and `.github/workflows/docs-deploy.yaml`.

The nested `docs/mkdocs.yml` mirrors the root navigation for partial builds. Prefer the root `mkdocs.yml` for the full public site. The `internal/` tree stays outside navigation.

## Contributing

- Follow the structure and naming above; use clear language without emojis
- Keep docs in sync with code; use proper Markdown and fix links when moving files
- When you change GitHub Actions, the **actionlint** workflow (see [reference/ci-reference.md](reference/ci-reference.md)) validates workflow YAML; Rust dependency policy is enforced by **cargo-deny** and root `deny.toml`
