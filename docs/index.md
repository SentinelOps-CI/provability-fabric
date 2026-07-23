# Provability Fabric documentation

Map for newcomers and operators. Prefer these entry points over digging through historical status pages.

## Start here

| Audience | First page | Then |
|----------|------------|------|
| **New users** | [Getting started (15 min)](getting-started.md) | [Local workflows](dev/local-workflows.md) |
| **Contributors** | [CONTRIBUTING.md](../CONTRIBUTING.md) | [Developer guide](guides/developer-guide.md) · [CI reference](reference/ci-reference.md) |
| **Operators** | [Runbooks](runbooks/README.md) | [Deployment](guides/deployment-guide.md) |
| **Science / lab** | [Proof-Carrying Science](pcs/README.md) | [Release checklist](pcs/release-checklist.md) |

Three clicks max for a warm local stack: **README → [getting-started](getting-started.md) → [local-workflows](dev/local-workflows.md)**.

## Information architecture

| Path | Role |
|------|------|
| [getting-started.md](getting-started.md) | First 15 minutes: CLI, wiring, Compose |
| [dev/local-workflows.md](dev/local-workflows.md) | Canonical Make / Just launch matrix |
| [guides/deployment-guide.md](guides/deployment-guide.md) | Canonical production deployment + trust-chain env |
| [guides/](guides/developer-guide.md) | How-to (develop, reuse, evidence walkthroughs) |
| [reference/](reference/ci-reference.md) | CLI, API, config, CI, errors |
| [architecture/](architecture/overview.md) | System design and guarantees |
| [roadmap/](roadmap/evidence-v0.2.md) | Living roadmap; completed status snapshots are archived |
| [runbooks/](runbooks/README.md) | Operations |
| [internal/](internal/README.md) | Maintainer-only; **one** [remediation tracker](internal/remediation-tracker.md) as status truth |
| [internal/archive/](internal/archive/README.md) | Historical audits and delivery stamps |

## Core platform

- [Architecture overview](architecture/overview.md)
- [CLI reference](reference/cli-reference.md)
- [Evidence and CERTs](evidence/overview.md)
- [Security](security/README.md)
- [Guarantees and non-claims](architecture/guarantees.md) | [Explicit non-claims](roadmap/evidence-v0.2-status.md#explicit-non-claims)
- [Dev Mode (E4)](features/dev-mode-e4.md) — console replay stream / DFA state

## Proof-Carrying Science (PCS)

- [PCS hub](pcs/README.md)
- [Release checklist](pcs/release-checklist.md)

## Integrations and adapters

- [MCP integration](integrations/mcp/integration.md)
- [Adapters overview](adapters/overview.md)
- [Reuse and extend](guides/reuse-and-extend.md)

## Benchmarks (SWE-bench)

- [bench/swebench/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/README.md)
- [experiments/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/README.md)

## Maintainer status (do not use archived counts)

| Live | Historical only |
|------|-----------------|
| [remediation-tracker.md](internal/remediation-tracker.md) | [internal/archive/](internal/archive/README.md) |
| [evidence-program-closure.md](roadmap/evidence-program-closure.md) | Old 8/67 | 13/68 snapshots |

## Build this site locally

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Open `http://127.0.0.1:8000`. Static output: `mkdocs build` → `./build/`.

Folder-level map (MkDocs, VS Code extension): [documentation-map.md](documentation-map.md).

## Repository layout (product tree)

See the root [README repository layout](../README.md#repository-layout) for which top-level directories remain and why. Marketing on-ramps, sample recipe stacks, LaTeX figures, and aspirational in-repo Terraform/Flux were removed in favor of `docs/`, `charts/`, `ops/` (observability only), and `scripts/dr/`.

## License

Apache 2.0. See [LICENSE](../LICENSE).
