# Evidence program closure

Single-page sign-off for the Evidence v0.1 + v0.2 vision and the repo-wide CI greening loop (2026-06-16).

## Vision status

| Program | Status | Reference |
|---------|--------|-----------|
| Evidence v0.1 | Complete on `main` | [evidence-v0.1-status.md](evidence-v0.1-status.md) |
| Evidence v0.2 | Complete on `main` | [evidence-v0.2.md](evidence-v0.2.md), [evidence-v0.2-status.md](evidence-v0.2-status.md) |
| CI hardening (#118) | Merged `3f150b15` | [ci-health-matrix](../internal/ci-health-matrix.md) |
| Post-merge smoke | Dispatched | [run 27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912) |

## Full-green CI criterion

Every workflow under `.github/workflows/` that triggers on **`push` to `main`** or **`schedule`** must have a latest `main` run with conclusion **success**. Track progress in [ci-health-matrix.md](../internal/ci-health-matrix.md) and via:

```bash
scripts/ci_workflow_inventory.sh
```

Reusable-only workflows (`workflow_call`) are tracked but not gating until invoked.

## Closure PR stack (2026-06-16)

| PR | Branch | Scope |
|----|--------|-------|
| #121 | `ci/standards-parity` | `upload-artifact@v4`, `STANDARDS_GITHUB_TOKEN` docs |
| #122 | `ci/platform-integration` | platform-replay, platform-cert, platform-perf, integration |
| #123 | `ci/bench-perf` | bench unit/smoke, performance-gate, slo-gates |
| #124 | `ci/security-compliance` | evidence.yaml, CodeQL JS |
| #126 | `ci/lean-research` | lean-offline, lean-morph, morph-replay, paper-conformance |
| #125 | `ci/nightly-batch` | nightly-replay, ci-nightly-pytest, redteam, chaos smoke |

## Org prerequisites (remaining blockers)

| Item | Owner | Verification |
|------|-------|----------------|
| `STANDARDS_GITHUB_TOKEN` | Org admin | `workflow_dispatch` Evidence v0.1 smoke — `make submodules` passes |
| `MORPH_API_KEY` (optional) | Org admin | Morph lean/replay jobs run instead of skip |
| `AWS_ROLE_ARN` + `EVIDENCE_BUCKET` (optional) | Org admin | `evidence.yaml` collect-evidence job runs |
| Branch protection required checks | Org admin | See commands below |

Setup steps: [CONTRIBUTING.md](../../CONTRIBUTING.md) and [ci-health-matrix — Required secrets](../internal/ci-health-matrix.md#required-secrets-org-prerequisites).

## Verification ceremony (Phase 6)

| Step | Command / action | Record |
|------|------------------|--------|
| Inventory on `main` | `scripts/ci_workflow_inventory.sh` | Exit code recorded below |
| Evidence smoke | `workflow_dispatch` `evidence-v01-smoke.yml` | [27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912) |
| Core CI | `workflow_dispatch` `ci.yml` | Run after stack merge |
| Fresh clone | [delivery checklist](evidence-v0.2-delivery.md#fresh-clone-verification-checklist) | Maintainer sign-off |

### Inventory run (2026-06-16)

`scripts/ci_workflow_inventory.sh` on `main` post-#118: **exit 1** (majority of push/schedule workflows still red; see matrix). Re-run after closure stack merges.

## Forward items (out of closure scope)

- Upstream `v1.0.0` tags for `verifiable-ai-ci/*` standards repos
- PCS `EvidenceBundle.v0` merge with Evidence JSON schemas (v0.3)
- Full Kind/Litmus chaos and platform docker-compose perf at scale

## Branch protection (attempted)

```bash
# Requires admin: org/repo settings
gh api repos/SentinelOps-CI/provability-fabric/branches/main/protection \
  --method PUT \
  -f required_status_checks[strict]=true \
  -f required_status_checks[checks][][context]='CI required checks' \
  -f required_status_checks[checks][][context]='evidence-schema-only' \
  -f required_status_checks[checks][][context]='smoke' \
  -f enforce_admins=true \
  -f required_pull_request_reviews[required_approving_review_count]=1
```

If the API returns 403, apply the same checks in **Settings → Branches → main** manually.
