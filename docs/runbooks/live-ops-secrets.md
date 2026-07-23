# Live ops (secret-gated)

Dispatch-only live paths for DR, registry publish, revocation sync, and edge load. CI-local moto/mock jobs remain the **gated push/schedule floor**. Live jobs **fail closed** when secrets or config are missing (no silent green).

Historical Wave 7 greening narrative: [wave7-post-merge-runbook.md](../internal/archive/wave7-post-merge-runbook.md). Tracker: [remediation-tracker.md](../internal/remediation-tracker.md).

## Separation rules

| Workflow | Gated floor (push/PR/schedule) | Live path |
|----------|--------------------------------|-----------|
| `dr-cross.yaml` | `mode=moto` (schedule Monday 09:00 UTC) | `workflow_dispatch` `mode=live` |
| `publish-updates.yaml` | dry-run package + HMAC + mock registry | `workflow_dispatch` `dry_run=false` |
| `revocation-sync.yaml` | dry-run mock fetch/merge/sign | `workflow_dispatch` `mode=live` |
| `edge-load.yaml` | smoke against local mock edge | `workflow_dispatch` `mode=full` |

Inventory exit 0 must **not** depend on production AWS or live registries. Adding secrets must not flip the Monday moto schedule into live DR.

## Required secrets

### Live DR (`dr-cross` mode=live)

| Secret | Purpose |
|--------|---------|
| `AWS_ACCESS_KEY_ID` / `AWS_SECRET_ACCESS_KEY` | AWS API (RDS describe, Route53, S3) |
| `DNS_ZONE_ID` | Route53 hosted zone for `db.provability-fabric.org` |
| `HEALTH_CHECK_ID` | Route53 health check disabled/enabled during failover/recovery |

RDS endpoints are resolved at runtime via `describe-db-instances` (`provability-fabric-primary` / `provability-fabric-secondary`). Sidecar health: `https://sidecar.provability-fabric.org/health`.

### Live registry publish (`publish-updates` dry_run=false)

| Secret | Purpose |
|--------|---------|
| `UPDATES_REGISTRY_URL` | HTTP PUT endpoint for signed `updates-package.tar.gz` |
| `PUBLISH_UPDATES_SIGNING_KEY` | HMAC key (must not be the CI-local default) |
| `UPDATES_REGISTRY_TOKEN` | Optional bearer token |
| `PUBLISH_UPDATES_METRICS_JSON` | Optional metrics JSON when Prometheus is unreachable |

Artifact `package-report.json` must show `live_registry: true`. `docs/updates.md` is updated via **PR**, not a direct push to `main`.

### Live revocation (`revocation-sync` mode=live)

| Secret | Purpose |
|--------|---------|
| `REVOCATION_REGISTRY_URL` | External registry JSON URL |
| `REVOCATION_SYNC_SIGNING_KEY` | HMAC signing key for merged list |
| `REVOCATION_REGISTRY_TOKEN` | Optional bearer token |

Produces `revocations.synced.json` + `live-sync-report.json` with `live_registry: true` and opens a review PR.

### Live edge load (`edge-load` mode=full)

| Secret | Purpose |
|--------|---------|
| `EDGE_REGION_URLS` | Comma-separated region base URLs (>=2 required) |
| `EDGE_LOAD_API_TOKEN` | Optional bearer for admin/purge |

## Dispatch commands

```bash
# Live DR (mutates Route53 health checks when simulate_failover=true)
gh workflow run dr-cross.yaml --ref main -f mode=live -f simulate_failover=true

# Live publish
gh workflow run publish-updates.yaml --ref main -f dry_run=false

# Live revocation sync
gh workflow run revocation-sync.yaml --ref main -f mode=live

# Live edge load
gh workflow run edge-load.yaml --ref main -f mode=full
```

## Success criteria

- Live job succeeds only with secrets present and real backends reachable.
- Dispatch without secrets exits non-zero (preflight / fail-closed).
- Package/sync artifacts label `live_registry=true` or `live_aws=true` / `live_edge=true`.
- Gated moto/mock jobs stay green on push/schedule independently of live secrets.

## Rollback

| Path | Rollback |
|------|----------|
| DR failover | Re-enable primary health check (`aws route53 update-health-check --no-disabled`); confirm DNS returns to primary |
| Publish PR | Close/reject the bot PR; do not merge `docs/updates.md` |
| Revocation PR | Close/reject; do not promote `revocations.synced.json` into `revocations.json` |
| Edge load | Stop the dispatch run; no infra mutation beyond traffic |
