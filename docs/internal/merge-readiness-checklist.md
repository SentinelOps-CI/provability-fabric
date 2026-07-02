# Merge Readiness Checklist (Phase 0)

Prerequisite for landing local audit remediation onto `main`. **Do not merge** until every gate below passes on an Ubuntu runner (local WSL or CI on the merge PR).

Source: [Audit Remediation Program](../roadmap/evidence-program-closure.md), reassessment [full-repo-audit-reassessment-2026-07-02.md](./full-repo-audit-reassessment-2026-07-02.md).

Last verified: **2026-07-02** (PR #144 branch-protection checks green; merge blocked by review only).

## Branch protection (merge gates)

Verified via `gh api repos/SentinelOps-CI/provability-fabric/branches/main/protection` on **2026-07-02**.

**Required status checks (exactly four):**

| Check | Merge gate |
|-------|------------|
| `CI required checks` | yes |
| `smoke` | yes |
| `evidence-schema-only` | yes |
| `Documentation Build` | yes |

**Also required:** at least **1 approving review** (`required_approving_review_count: 1`).

**Not merge gates** (informational on PRs; do not block merge when red):

| Workflow / check | Notes |
|------------------|-------|
| `Lean Offline Build` | Optional; cold mathlib cache can hit the 45m runner cap. Runs on `schedule`, `workflow_dispatch`, and path-filtered `push` to `main`/`develop` only (no `pull_request`). |
| `Paper Conformance CI` | Optional heavy suite; `scheduler-clock` can timeout on cold cache. Runs on `schedule`, `workflow_dispatch`, and path-filtered `push` only (no `pull_request`). |
| `actionlint`, CodeQL, `integration`, `deny`, etc. | Subsumed by or separate from the four gates above; red status is triage signal, not a branch-protection block unless listed in the table above. |

**When all four branch-protection checks are green:** merge is unblocked by CI and blocked only by the missing approving review.

## PR #144 CI snapshot (2026-07-02)

**Branch:** `audit-remediation-merge`. **PR:** [#144](https://github.com/SentinelOps-CI/provability-fabric/pull/144).

| Gate | Status | Notes |
|------|--------|-------|
| `CI required checks` | pass | Required |
| `smoke` | pass | Required |
| `evidence-schema-only` | pass | Required |
| `Documentation Build` | pass | Required |
| `Lean Offline Build` | fail (optional) | Vendor mathlib on cold cache; ~45m runner kill; not a merge gate |
| `Scheduler & Clock Model` (paper-conformance) | cancelled (optional) | Job timeout on cold cargo cache; not a merge gate |
| Approving review | **missing** | `mergeStateStatus: BLOCKED`, `reviewDecision: REVIEW_REQUIRED` |

**Merge state:** **CI clear** — all four branch-protection checks green. **Merge blocked by review only** until an approver signs off.

## Pre-merge (local / PR branch)

- [x] Resolve merge conflicts with `main` (branch `audit-remediation-merge` rebased/current)
- [x] Open merge PR(s); request review — [PR #144](https://github.com/SentinelOps-CI/provability-fabric/pull/144)
- [x] Submodule `external/TRACE-REPLAY-KIT` at pinned commit with Dockerfile `CMD []` (F10) — `957630f`
- [x] Run Linux validation script (Windows: skip Docker/replay; see notes below):

```bash
bash scripts/linux_validation_checklist.sh
```

Equivalent manual commands:

```bash
cargo test -p retrieval-gateway
PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests
cd runtime/ledger && npm ci && npm test && npm run typecheck:server
tests/replay/test_docker_invocation.sh   # requires Docker + submodule
python scripts/count_sidecar_unwraps.py --max 10
python scripts/count_ledger_any.py --max 20
python scripts/audit_ci_honesty.py
python tests/crypto/test_cross_lang_dsse.py
make no-runtime-placeholders
make docs-strict
```

**Windows local results (2026-07-03):**

| Command | Exit | Notes |
|---------|------|-------|
| `cargo test -p retrieval-gateway` | 0 | 14 tests |
| `PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests` | 0 | 9 tests |
| `cd runtime/ledger && npm test && npm run typecheck:server` | 0 | 23 passed, 1 skipped |
| `tests/replay/test_docker_invocation.sh` | skip | Docker not available on Windows |
| `python scripts/count_sidecar_unwraps.py --max 10` | 0 | 0 unwraps |
| `python scripts/count_ledger_any.py --max 20` | 0 | 0 `any` |
| `python scripts/audit_ci_honesty.py` | 0 | 0 unjustified |
| `python tests/crypto/test_cross_lang_dsse.py` | 0 | cross-lang DSSE |
| `make no-runtime-placeholders` | 0 | |
| `make docs-strict` | 0 | after internal doc link fixes |

## Submodule bump (F10)

- [x] `tools/standards/versions.json` pin matches `external/TRACE-REPLAY-KIT` HEAD (`957630f1ab8c00031c5f56d32e610a9f8baf69b6`)
- [x] `external/TRACE-REPLAY-KIT/runner/Dockerfile` uses `ENTRYPOINT ["python", "replay_run.py"]` and `CMD []`
- [x] `tests/replay/test_docker_invocation.sh` exits 0 on Linux CI — **pass** on PR run [28576347480](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347480) (`replay-tests` job)
- [ ] `integration.yaml` submodule init + full F06/F10/F21 suite — **fail** on PR run [28576347398](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576347398) (submodule clone; fixed in branch via `make submodules` + token)

## CI wiring verified on PR

- [x] `platform-replay.yml` — replay docker contract test step wired
- [x] `integration.yaml` — replay contract test step + `test_ledger_mcp_tenant.py` + compose smoke
- [x] `reusable-ci-rust.yml` — `integration_tests` + regression gates + `retrieval-gateway`
- [x] `reusable-ci-extended.yml` — `test_cross_lang_dsse.py` (F01)
- [x] `ci.yml` — `audit_ci_honesty.py` gate
- [x] `retrieval-gateway.yml` — build + test on path trigger (F05)
- [x] Placeholder gate: `make no-runtime-placeholders` exit 0 (excludes `build/`, `dist/`, binaries)
- [x] `replay.yml` — F10 docker contract test added (preemptive Wave 7 triage)

## Post-merge (main — do NOT skip)

- [x] Refresh CI inventory baseline (2026-07-03; `main` still 12/68 green until merge):

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
```

- [ ] Two consecutive green runs on replay cluster (5 workflows)
- [ ] Two consecutive green runs on security cluster (CodeQL, cargo-deny)
- [ ] Update [remediation-tracker.md](./remediation-tracker.md) and [evidence-program-closure.md](../roadmap/evidence-program-closure.md)

## Explicit non-actions (per program)

- **No force-merge to `main`** without green Linux gates above
- **No weakening** Lean enforced sorry set or vacuous test gates
- **No `passWithNoTests`** in required marketplace workflow

## Target milestone M1

~20/67 gated workflows green after replay + security clusters unlock.

## Merge approval

**Merge to `main` requires explicit user approval** after PR #144 shows all four branch-protection checks green (currently satisfied) and an approving review is recorded.

<details>
<summary>PR #144 CI snapshot (2026-07-03, historical — superseded)</summary>

**Branch:** `audit-remediation-merge` @ `3d4bc35b`. Prior triage before required checks went green.

| Check | Status | Notes |
|-------|--------|-------|
| `CI required checks` | fail (blocked) | Awaited `ci-rust`, `ci-go-node`, `ci-extended` |
| `integration` | fail | `Cargo.lock` gitignored |
| `ci-go-node / go-node` | fail | `runtime/ledger/package-lock.json` out of sync |

</details>
