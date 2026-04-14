# Verifiable MCP fraud demo

TypeScript demo that exercises MCP-style flows against the SentinelOps platform SDK. Lives under the Provability Fabric monorepo.

## Repository

Upstream: **[github.com/SentinelOps-CI/provability-fabric](https://github.com/SentinelOps-CI/provability-fabric)**.

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric/demos/verifiable-mcp-fraud
npm ci
```

The package depends on `core/sdk/typescript` via a local `file:` reference; run commands from this directory inside a full clone.

## Scripts

- `npm run build` — compile TypeScript
- `npm run dev` — run MCP server (ts-node)
- `npm run dev:agent` / `npm run dev:simulator` — agent and simulator entrypoints
- `npm run demo` — setup then run scripted demo

See [docs/guides/demos.md](../../docs/guides/demos.md) for broader demo documentation.
