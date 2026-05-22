# Provability Fabric documentation

Provability Fabric is an open-source framework for **provable agent behavior**: specifications and Lean proofs tied to what runs in production, runtime enforcement, and evidence you can replay and verify.

## Start here

| Audience | Start with |
|----------|--------------|
| New users | [Getting started](guides/getting-started.md) |
| Operators | [Runbooks](runbooks/README.md) · [Deployment](guides/deployment-guide.md) |
| Contributors | [Developer guide](guides/developer-guide.md) · [CI reference](reference/ci-reference.md) |
| Science / lab workflows | [Proof-Carrying Science](pcs/README.md) |

## Major areas

### Core platform

- [Architecture overview](architecture/overview.md) — components and design
- [CLI reference](reference/cli-reference.md) — `pf` commands
- [Evidence and CERTs](evidence/overview.md) — formats, validation, replay
- [Security](security/README.md) — threat model, signing, supply chain

### Proof-Carrying Science (PCS)

Provability Fabric can verify and sign **science claim bundles** (lab QC release, tool-use safety, reproducible computation) and run **release admission benchmarks**.

- [PCS hub](pcs/README.md) — quickstart, verification, benchmarks, fixtures
- [Release checklist](pcs/release-checklist.md) — pre-release verification

### Integrations and adapters

- [MCP integration](integrations/mcp/integration.md)
- [Adapters overview](adapters/overview.md) — HTTP/file adapters and solver integrations
- [Reuse and extend](guides/reuse-and-extend.md) — minimal CLI-only setups

### Benchmarks (SWE-bench)

Agent benchmark workflows are documented in the repository (not only in this site):

- [bench/swebench/README.md](../bench/swebench/README.md)
- [experiments/README.md](../experiments/README.md)

## Build this site locally

From the repository root:

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Open `http://127.0.0.1:8000`. Static output: `mkdocs build` → `./build/`.

See [docs/README.md](README.md) for the full documentation map. Contributor-only notes live under [internal/](internal/) and are omitted from the published navigation.

## License

Apache 2.0 — see [LICENSE](../LICENSE).
