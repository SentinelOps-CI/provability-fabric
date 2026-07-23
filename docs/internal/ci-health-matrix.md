# CI health matrix (redirect)

> **Archived.** Full historical triage: [archive/ci-health-matrix.md](archive/ci-health-matrix.md).

## Live posture

| Source | Role |
|--------|------|
| [remediation-tracker.md](remediation-tracker.md) | Authoritative findings / wave status |
| [evidence-program-closure.md](../roadmap/evidence-program-closure.md) | Gated CI counts and inventory exit |
| [ci-inventory-latest.md](ci-inventory-latest.md) | Latest inventory markdown dump |
| [live-ops-secrets.md](../runbooks/live-ops-secrets.md) | Secret-gated DR / publish / revocation / edge-load |

Re-run inventory:

```bash
scripts/ci_workflow_inventory.sh --markdown
# Windows: powershell -File scripts/ci_workflow_inventory.ps1 -Markdown
```

## Required secrets (org prerequisites)

### `STANDARDS_GITHUB_TOKEN` setup (org admin)

| Step | Action |
|------|--------|
| 1 | Create PAT (fine-grained or classic) with **read** on `verifiable-ai-ci/CERT-V1` and `verifiable-ai-ci/TRACE-REPLAY-KIT` |
| 2 | Repo **Settings → Secrets and variables → Actions → New repository secret** |
| 3 | Name `STANDARDS_GITHUB_TOKEN`, paste PAT |
| 4 | Local check: `STANDARDS_GITHUB_TOKEN=<pat> make dev-standards` |
| 5 | CI check: dispatch **Evidence v0.1 smoke** or **Standards Pin Drift Check** — `make submodules` must pass |

Contributor-facing steps: [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md).

| Secret / service | Notes |
|------------------|-------|
| `STANDARDS_GITHUB_TOKEN` | Required for Evidence smoke, cert/replay/docs build, standards-pin, egress, nightly-replay |
| `GITHUB_TOKEN` | Auto-provided |
| `CI_PAT` | Optional; release cross-repo dispatch |
| `AWS_*` | Optional; live DR / evidence collection only |

## Local pre-PR gates

```bash
make dev-standards
make evidence-verify   # Evidence changes
make docs-strict       # docs/** or mkdocs.yml
make check-wiring      # compose ↔ code defaults
```

See [ci-reference.md](../reference/ci-reference.md).
