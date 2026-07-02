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
scripts/ci_workflow_inventory.sh --markdown   # docs/internal/ci-inventory-latest.md
# Windows: scripts/ci_workflow_inventory.ps1 -Markdown
```

**Current posture (2026-07-03, Wave 7):** Local audit remediation program complete for code gates (unwrap **0**, ledger `any` **0**, CI honesty **0** unjustified, Invariants.lean **0 sorry** + CI-enforced, `proofs/Policy.lean` **0 sorry**). Evidence lane remains **green** on `main`. Repo-wide CI is **not** fully green — inventory reports **13/68** gated workflows green. **PR #144 not merged** — blocked on CI run [28576347710](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347710); fixes pushed for `deny.toml`, `integration.yaml` submodule init, and docs-strict links. See [merge-readiness-checklist.md](../internal/merge-readiness-checklist.md), [wave7-post-merge-runbook.md](../internal/wave7-post-merge-runbook.md), and [full-repo-audit-reassessment-2026-07-03.md](../internal/full-repo-audit-reassessment-2026-07-03.md).

**Do not claim 68/68** until `scripts/ci_workflow_inventory.sh` exits 0 twice consecutively on `main`.

### Path to 67/67 (Wave 7 — updated 2026-07-02)

| Milestone | Target green | Clusters | Depends on |
|-----------|-------------:|----------|------------|
| M1 (post-Phase 0–1 merge) | ~20/67 | Replay + Security | Linux replay contract test on `main`; submodule bump |
| M2 | ~25/68 | + Lean (paper-conformance) partial | F24 rate-limit + integration_tests in CI with `PF_SHADOW_MODE=1`; Invariants.lean sorry-free; lean-style mathlib cache; merge to main |
| M3 | ~35/67 | + Platform | `integration.yaml` F06 smokes; operational-excellence real paths |
| M4 | ~50/67 | + Bench + Docs | Criterion baseline on main; `docs-build.yaml` green |
| M5 | 67/67 | Remaining ~30 | Weekly inventory diff; one workflow per PR |

1. **Replay cluster** — fix Docker replay runner CLI (F10); unlock 5 workflows after Linux validation.
2. **Security cluster** — CodeQL artifact chain (F20 done locally); cargo-deny all-features; wasm-scan empty-registry skip.
3. **Lean cluster** — vendor mathlib cache without stale `.git`; Invariants.lean **sorry-free** (2026-07-03); Policy tree sorry burn-down continues per [lean-sorry-burn-down.md](../internal/lean-sorry-burn-down.md); paper-conformance rate-limits + `integration_tests` with `PF_SHADOW_MODE=1`.
4. **Platform cluster** — SLO lockfiles (F19 done); `integration.yaml` F06 smoke scope; billing/operational-excellence.
5. **Bench cluster** — Criterion baseline refresh (F23 workflow ready); performance-gate thresholds.
6. **Remaining ~30** — triage via weekly `ci_workflow_inventory.sh --markdown` diff in [ci-inventory-latest.md](../internal/ci-inventory-latest.md).

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
| #128 | `ci/post-closure-hotfixes` | actionlint/docs-build/cert-validate hotfixes — **merged** `de104223` (2026-06-16) |

## Org prerequisites (remaining blockers)

| Item | Owner | Verification |
|------|-------|----------------|
| `STANDARDS_GITHUB_TOKEN` | Org admin | **Configured** (2026-06-14). Re-verify: `workflow_dispatch` Evidence v0.1 smoke — `make submodules` passes |
| `MORPH_API_KEY` (optional) | Org admin | Morph lean/replay jobs run instead of skip |
| `AWS_ROLE_ARN` + `EVIDENCE_BUCKET` (optional) | Org admin | `evidence.yaml` runs `collect-evidence` instead of offline report |
| Branch protection required checks | Org admin | **Applied** via `gh api` (2026-06-16): CI required checks, smoke, evidence-schema-only, Documentation Build |

Setup steps: [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md) and [ci-health-matrix — Required secrets](../internal/ci-health-matrix.md#required-secrets-org-prerequisites).

## Verification ceremony (Phase 6)

| Step | Command / action | Record |
|------|------------------|--------|
| Inventory on `main` | `scripts/ci_workflow_inventory.sh` | Exit code recorded below |
| Evidence smoke | `workflow_dispatch` `evidence-v01-smoke.yml` | [27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912), [27597765777](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765777) |
| Core CI | `workflow_dispatch` `ci.yml` | [27597765883](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765883) |
| Fresh clone | [delivery checklist](evidence-v0.2-delivery.md#fresh-clone-verification-checklist) | Maintainer sign-off |

### Inventory run (2026-06-16)

| Pass | Gated | Green | Red | Unknown |
|------|------:|------:|----:|--------:|
| Post-#127 | 67 | 6 | 56 | 21 |
| Post-#128 (`de104223`) | 67 | 8 | 56 | 21 |

`scripts/ci_workflow_inventory.sh` on `main` after **#128** merge: **exit 1** (full-green criterion not met). Gains include `proto-compat.yaml` success; remaining red lanes are path-filtered push failures, optional AWS/Morph secrets, and infra-heavy Kind/Litmus jobs. Post-#128 ceremony dispatches: Evidence smoke [27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269), CI [27616317486](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616317486).

### Acceptance re-verify (2026-06-17)

| Pass | Gated | Green | Red | Unknown |
|------|------:|------:|----:|--------:|
| Post-#132 (`0d802f6e`) | 67 | 12 | 52 | 21 |
| Post-#134 (`f55a98bd`) | 67 | 12 | 52 | 21 |
| Audit snapshot (2026-07-02) | 67 | 13 | 53 | 19 |
| Phase 0 refresh + F33/F24 (2026-07-02 local) | 67 | 13 | 53 | 19 |
| Wave 7 execution (2026-07-03) | 68 | 13 | 55 | — |

**PR #144:** not merged. CI snapshot run [28576347710](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347710). Key PR passes: `ci-honesty` [28576347710](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347710), `replay-tests` [28576347480](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347480), `retrieval-gateway` [28576347539](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347539), `Lean Style Check` [28576347346](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347346).

### Path to 67/67 (Wave 7)

1. **Replay cluster** — fix Docker replay runner CLI (F10); unlock 5 workflows.
2. **Security cluster** — CodeQL artifact chain (F20); cargo-deny all-features; wasm-scan empty-registry skip.
3. **Lean cluster** — vendor mathlib cache; scoped sorry aligned with [lean-sorry-burn-down.md](../internal/lean-sorry-burn-down.md).
4. **Platform cluster** — SLO lockfiles (F19 done); operational-excellence ghost tests (F06 done); billing/integration smoke.
5. **Bench cluster** — Criterion baseline refresh (F23); performance-gate thresholds.
6. **Remaining ~30** — triage via weekly `ci_workflow_inventory.sh --markdown` diff in [ci-health-matrix.md](../internal/ci-health-matrix.md).

_Superseded by milestone table above (2026-07-02 refresh)._

Track per-finding status in [remediation-tracker.md](../internal/remediation-tracker.md). Closure sign-off updates this page only when inventory exits **0**.

Local maintainer gates on `main`: `make dev-standards`, `make standards-pin-check`, `make evidence-verify`, `make docs-strict` — all pass (2026-06-17 re-verify). Evidence smoke on `main`: [27670516771](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27670516771) (success); ceremony baseline [27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269) (success). Four gap-closure workflow fixes merged via **PR #134** (`ci/gap-closure-workflow-bumps`).

Deep replay acceptance archive (private, local): `private/acceptance-evidence/acceptance-2026-06-16/evidence-v02-replay-report.json` — excerpt `status: pass`, `execute_status: pass`, `low_view_result: pass` (regenerated on maintainer host 2026-06-16; gitignored).

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
