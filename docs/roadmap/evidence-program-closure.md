# Evidence program closure

Single-page sign-off for the Evidence v0.1 + v0.2 vision and the repo-wide CI greening loop (2026-06-16).

## Vision status

| Program | Status | Reference |
|---------|--------|-----------|
| Evidence v0.1 | Complete on `main` | [evidence-v0.1-status.md](evidence-v0.1-status.md) |
| Evidence v0.2 | Complete on `main` | [evidence-v0.2.md](evidence-v0.2.md), [evidence-v0.2-status.md](evidence-v0.2-status.md) |
| CI hardening (#118) | Merged `3f150b15` | [ci-health-matrix](../internal/ci-health-matrix.md) |
| Post-merge smoke | Dispatched | [run 27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912) (post-#118), [27597765777](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765777) — **success** (Phase 6 ceremony) |
| Core CI dispatch | Dispatched | [run 27597765883](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765883) — **success** (Phase 6 ceremony) |

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
| #127 | `docs/evidence-program-closure` | Closure sign-off page, CHANGELOG entry |
| #128 | `ci/post-closure-hotfixes` | actionlint/docs-build/cert-validate hotfixes (**open** — needs approving review) |

## Org prerequisites (remaining blockers)

| Item | Owner | Verification |
|------|-------|----------------|
| `STANDARDS_GITHUB_TOKEN` | Org admin | **Configured** (2026-06-14). Re-verify: `workflow_dispatch` Evidence v0.1 smoke — `make submodules` passes |
| `MORPH_API_KEY` (optional) | Org admin | Morph lean/replay jobs run instead of skip |
| `AWS_ROLE_ARN` + `EVIDENCE_BUCKET` (optional) | Org admin | `evidence.yaml` runs `collect-evidence` instead of offline report |
| Branch protection required checks | Org admin | **Applied** via `gh api` (2026-06-16): CI required checks, smoke, evidence-schema-only, Documentation Build |

Setup steps: [CONTRIBUTING.md](../../CONTRIBUTING.md) and [ci-health-matrix — Required secrets](../internal/ci-health-matrix.md#required-secrets-org-prerequisites).

## Verification ceremony (Phase 6)

| Step | Command / action | Record |
|------|------------------|--------|
| Inventory on `main` | `scripts/ci_workflow_inventory.sh` | Exit code recorded below |
| Evidence smoke | `workflow_dispatch` `evidence-v01-smoke.yml` | [27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912), [27597765777](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765777) |
| Core CI | `workflow_dispatch` `ci.yml` | [27597765883](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765883) |
| Fresh clone | [delivery checklist](evidence-v0.2-delivery.md#fresh-clone-verification-checklist) | Maintainer sign-off |

### Inventory run (2026-06-16)

`scripts/ci_workflow_inventory.sh` on `main` post-closure stack (#121–#127): **exit 1** — 67 gated (push/schedule) workflows, 6 green, 56 red, 23 unknown/no-run (summary from full inventory pass). Evidence smoke and standards-pin green; remaining red lanes are path-filtered push failures, optional AWS/Morph secrets, and infra-heavy Kind/Litmus jobs. Re-run after post-#127 hotfixes land on `main`.

Use Git Bash on Windows (`export PATH="/c/Program Files/GitHub CLI:$PATH"`) — WSL `bash` may not see `gh`.

## Forward items (out of closure scope)

- Upstream `v1.0.0` tags for `verifiable-ai-ci/*` standards repos
- PCS `EvidenceBundle.v0` merge with Evidence JSON schemas (v0.3)
- Full Kind/Litmus chaos and platform docker-compose perf at scale

## Branch protection (applied 2026-06-16)

Required status checks on `main`: **CI required checks**, **smoke**, **evidence-schema-only**, **Documentation Build**; 1 approving review; enforce admins.

Re-apply or extend checks:

```bash
# Requires admin: org/repo settings
gh api repos/SentinelOps-CI/provability-fabric/branches/main/protection \
  --method PUT --input - <<'EOF'
{
  "required_status_checks": {
    "strict": true,
    "checks": [
      {"context": "CI required checks"},
      {"context": "smoke"},
      {"context": "evidence-schema-only"},
      {"context": "Documentation Build"}
    ]
  },
  "enforce_admins": true,
  "required_pull_request_reviews": {
    "required_approving_review_count": 1
  },
  "restrictions": null
}
EOF
```

Pipe JSON via stdin on Windows PowerShell: `Get-Content .mlc-tmp/branch-protection.json -Raw | gh api ... --input -`
