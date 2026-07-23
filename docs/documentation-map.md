# Provability-Fabric Documentation

This directory contains the documentation for the Provability-Fabric framework.

## Structure (canonical)

| Section | Purpose |
|---------|---------|
| **[index.md](index.md)** | Docs home / newcomer TOC |
| **[getting-started.md](getting-started.md)** | First 15 minutes |
| **dev/** | Local workflows, Lean build |
| **guides/** | How-to (deployment, developer, reuse, evidence) |
| **guides/deployment-guide.md** | Canonical deployment + trust-chain env (`production-deployment.md` is a stub) |
| **features/** | Accurate feature notes only (Dev Mode); marketing write-ups → `internal/archive/` |
| **reference/** | CLI, API, CI, configuration |
| **architecture/** | System design and guarantees |
| **roadmap/** | Living roadmap (completed status → `internal/archive/`) |
| **runbooks/** | Operations |
| **internal/** | Maintainer-only; [remediation-tracker.md](internal/remediation-tracker.md) is status truth |
| **internal/archive/** | Historical audits and delivery stamps |
| **specs/** / **evidence/** / **security/** / **pcs/** / … | Domain docs as before |

**Bench (SWE-bench)** docs live at `bench/swebench/README.md` and `experiments/README.md`.

## Entry points

- **[index.md](index.md)** — Documentation home
- **[getting-started.md](getting-started.md)** — First 15 minutes
- **[dev/local-workflows.md](dev/local-workflows.md)** — Make / Just launch matrix
- **[guides/getting-started.md](guides/getting-started.md)** — Longer concepts + first agent
- **[guides/deployment-guide.md](guides/deployment-guide.md)** — Canonical deployment
- **[features/dev-mode-e4.md](features/dev-mode-e4.md)** — Console Dev Mode (E4)
- **[architecture/overview.md](architecture/overview.md)** — System architecture
- **[evidence/overview.md](evidence/overview.md)** — Evidence and CERTs
- **[pcs/README.md](pcs/README.md)** — Proof-Carrying Science

## Building

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Output directory: **`build/`**. Canonical config is the **repository-root** `mkdocs.yml` only (`docs/mkdocs.yml` is a stub). The `internal/` tree stays outside published navigation.

## Contributing

Keep docs in sync with code; fix links when moving files. Historical status belongs under `internal/archive/`, not as competing live truth. Workflow YAML: [reference/ci-reference.md](reference/ci-reference.md).
