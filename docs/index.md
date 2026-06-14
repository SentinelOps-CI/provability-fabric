# Provability Fabric documentation

Provability Fabric is an open-source framework for **provable agent behavior**. Specifications and Lean proofs connect to production runtime enforcement, and evidence packages support replay and verification.

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

Provability Fabric verifies and signs **science claim bundles** for lab QC release, tool-use safety, and reproducible computation. It also runs **release admission benchmarks** that score admit and reject behavior.

- [PCS hub](pcs/README.md) — quickstart, verification, benchmarks, fixtures
- [Release checklist](pcs/release-checklist.md) — pre-release verification

### Integrations and adapters

- [MCP integration](integrations/mcp/integration.md)
- [Adapters overview](adapters/overview.md) — HTTP/file adapters and solver integrations
- [Reuse and extend](guides/reuse-and-extend.md) — minimal CLI-only setups

### Benchmarks (SWE-bench)

Agent benchmark workflows are documented in the repository alongside this site.

- [bench/swebench/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/bench/swebench/README.md)
- [experiments/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/experiments/README.md)

## Build this site locally

From the repository root, install dependencies and start the preview server.

```bash
pip install -r docs/requirements.txt
mkdocs serve
```

Open `http://127.0.0.1:8000` in your browser. A static build writes to `./build/` when you run `mkdocs build`.

See [documentation map](documentation-map.md) for the full documentation map. Contributor-only notes live under [internal/README.md](internal/README.md) and stay outside the published navigation.

## License

Apache 2.0. See [LICENSE](../LICENSE).
