# ops/

Lean observability and retention assets used by local Compose and retention tests.

| Path | Purpose |
|------|---------|
| `grafana/` | Dashboards + provisioning mounted by `docker-compose.yml` |
| `prometheus/` | Scrape config mounted by Compose |
| `retention/` | Data retention manager + unit tests |

Kubernetes CRDs/Flux, in-repo Terraform, and TUF stubs were removed. Deploy with [`charts/pf-enforce`](../charts/pf-enforce); DR proof lives under [`scripts/dr/`](../scripts/dr/) and `.github/workflows/dr-cross.yaml`.
