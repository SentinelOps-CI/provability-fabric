# Ledger Consolidation RFC

Status: **Accepted** (Wave 4, 2026-07-01)

## Problem

The ledger service has three divergent entrypoints (`index.ts`, `index-simple.ts`, `index-production.ts`) with ~60–70% duplicated GraphQL schema, resolvers, and REST routes. Docker runs `index-simple.js` (no MCP), while `package.json start` targets `index.js`. MCP proxy reads `tenant_id` but auth middleware sets `tid`. Zero Jest tests and a broken Prisma performance migration compound operational risk.

## Goals

1. One shared server library with profiled bootstraps (`dev`, `production`).
2. Docker and `npm start` both run MCP-enabled production profile.
3. Unified tenant claim: `tid` canonical; MCP layers accept `tid` or `tenantId`.
4. Deny-by-default MCP method policy; tool signatures validated against pre-registered allow-list only.
5. Real Jest coverage on receipts, MCP deny paths, and tenant scoping.

## Non-goals

- Merging `auth-production.ts` rate-limit matrix into dev profile.
- Full Ed25519 receipt verification (Wave 2 trust chain).
- Deleting `index-simple.ts` / `index-production.ts` in this wave (thin re-exports retained for compatibility).

## Target layout

```
runtime/ledger/src/
  server/
    schema.ts          # GraphQL typeDefs (single source)
    resolvers.ts       # Tenant-scoped resolvers factory
    rest-routes.ts     # Shared REST endpoints
    types.ts           # UserContext, ServerDeps
  profiles/
    dev.ts             # auth-simple, seed tenants, no MCP
    production.ts        # auth + MCP + WebSocket
  mcp/                 # unchanged module tree
  index.ts             # PROFILE=dev|production bootstrap
  index-simple.ts      # re-export dev profile
  index-production.ts  # re-export production profile
```

## Profile matrix

| Capability | `dev` | `production` |
|------------|-------|--------------|
| Auth | `auth-simple` (mock JWT / dev tenant) | `auth` + `auth-production` JWT |
| MCP + WebSocket | No | Yes (`McpService`) |
| Default port | 8080 | 4000 |
| Seed tenants | Yes | No |
| GraphQL auth | `userFromRequest` / mock | `authMiddleware` + `tenantMiddleware` |

## Bootstrap

`index.ts` reads `PROFILE` (default `production`):

```bash
PROFILE=dev npx tsx src/index.ts
PROFILE=production node dist/index.js   # Docker CMD
```

## Docker alignment

```dockerfile
ENV PROFILE=production
CMD ["sh", "-c", "npx prisma migrate deploy && node dist/index.js"]
```

## Tenant context contract

Auth middleware sets `req.user.tid` (canonical). MCP proxy resolves:

```typescript
const tenantId = user?.tid ?? user?.tenantId ?? user?.tenant_id;
```

## MCP policy

- Unknown JSON-RPC methods: **deny** in `enforceMethodPolicy`.
- Tool signatures: validate against `allowedTools` populated at init only; `validateToolCall` must not self-register signatures.
- `forwardToMcpServer`: return explicit `501` when backend handler absent (no silent mock success in production path).

## Prisma migration hygiene

`20250101000000_optimize_performance` references non-existent columns (`created_at` on `UsageEvent`, `TenantInvoice`, `deleted_at`, etc.). **Quarantined** under `prisma/quarantine/` — not applied by `prisma migrate deploy`.

## Testing

Jest suite under `src/**/*.test.ts`:

- `receipts.test.ts` — structural signature verification
- `mcp-proxy.test.ts` — unknown method deny, allowed methods pass policy gate
- `resolvers.test.ts` — `updateCapsule` enforces `tenantId` in where clause

## Rollout

1. Land shared `server/` + profiles (this PR).
2. Wire CI: `npm test` in `runtime/ledger` on PR.
3. Wave 2: wire DSSE verify into `verifyReceiptSignature`.
4. Retire duplicate resolver copies after one release cycle.

## References

- Audit findings F03, F04, F09, F11, F22, F26–F28
- [full-repo-audit-2026-07-01.md](./full-repo-audit-2026-07-01.md)
