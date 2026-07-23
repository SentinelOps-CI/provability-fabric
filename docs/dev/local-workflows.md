# Local workflows

Canonical launch matrix for day-to-day engineering. Prefer these Make / `just` targets over ad-hoc `docker compose` flags so ports and profiles stay aligned.

Lean / mathlib builds are out of scope here — see [lean-build.md](lean-build.md).

## Quick reference

| Task | Command | Services | Ports |
|------|---------|----------|-------|
| Platform only (default) | `make platform-up` or `just up platform` | postgres, redis, API/spec/proof/build/evidence/replay, sidecar | API `:8000`, sidecar `:8006` |
| Rebuild images then platform | `make platform-up-build` | same as platform | same |
| Ledger GraphQL loop | `make ledger-up` or `just up ledger` | default profile + ledger (`PROFILE=dev`) | ledger `:4000`, sidecar `:8006` |
| Enforcement (egress) | `make enforcement-up` | default + egress-firewall | firewall `:8081` |
| Full stack (console + demos) | `make full-up` or `just up full` | `--profile full` | console `:3000`, ledger `:4000`, grafana `:3003`, demo `:3001` |
| Sidecar only (local cargo) | `just up sidecar` | documents `cargo run` in `runtime/sidecar-watcher` | `:8006` |
| Tool broker (local cargo) | `just up broker` | documents `cargo run` with compose-aligned kernel URL | kernel `http://localhost:8006` |
| Compose smoke | `make compose-smoke` | postgres, redis, sidecar, ledger, retrieval-gateway | asserts `/health` |
| Wiring check | `make check-wiring` | none (static) | compose ↔ code defaults |

Warm paths omit `--build`. Health readiness uses `docker compose up --wait` (no fixed `sleep 30`).

## Port / URL contract (local)

| Service | Host URL | Notes |
|---------|----------|-------|
| Ledger | `http://localhost:4000` | GraphQL + `/health`; compose sets `PROFILE=dev` |
| Sidecar / policy kernel | `http://localhost:8006` | MCP and tool-broker check this port |
| API gateway | `http://localhost:8000` | Default platform (`services/api-gateway` + backends) |
| Console | `http://localhost:3000` | **Full profile only** — nginx proxies `/api` to the gateway |
| Egress firewall | `http://localhost:8081` | Enforcement / full profile |

Run `make check-wiring` (or `python scripts/check_wiring.py`) after changing compose env or code defaults.

## Platform APIs (default Compose)

```bash
make platform-up          # or: just up platform
curl -sf http://localhost:8000/health
```

Backends (host ports): spec `:8001`, proof `:8002`, build `:8003`, evidence `:8004`, replay `:8005`, sidecar `:8006`.

## Console (full profile)

Admin UI for policies, evidence, replay, and Dev Mode. Nginx in the console image proxies `/api` to `api-gateway:8000` (same-origin from the browser).

```bash
make full-up              # or: just up full
# open http://localhost:3000
```

Local Node (without Docker), with platform already on `:8000`:

```bash
cd console
npm ci || npm install --no-audit --no-fund
npm start                 # CRA; package.json proxy → http://localhost:8000
```

## Ledger without Docker

```bash
cd runtime/ledger
npm install
npm run dev              # PROFILE=dev (auth-simple, no MCP boot)
npm run dev:production   # prod-like JWT + MCP
npm run dev:minimal      # minimal-server.js — local demo only, not production
```

Point MCP / SDK clients at `http://localhost:4000`. Sidecar for local MCP checks: `SIDECAR_URL=http://localhost:8006`.

Docs site (repo root, after `pip install -r docs/requirements.txt`): `make docs-serve` → `http://127.0.0.1:8002`.

## Tool broker (warm path)

Under compose `--profile full`, tool-broker restarts with `unless-stopped`. Locally:

```bash
cd runtime/tool-broker
KERNEL_URL=http://localhost:8006 cargo run
```

## Just wrappers

```bash
just up platform   # → make platform-up
just up ledger     # → make ledger-up
just up sidecar    # prints cargo recipe for sidecar
just up broker     # prints cargo recipe for tool-broker
just up full       # → make full-up
```

## Related

- Compose profiles: root [`docker-compose.yml`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/docker-compose.yml)
- Env schema: [`schemas/pf-env.schema.json`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/schemas/pf-env.schema.json)
- Contributing overview: [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md)
- Dev Mode (console `/dev`): [dev-mode-e4.md](../features/dev-mode-e4.md)
