# Full Repository Audit — Reassessment Report v2 (2026-07-03)

Post-remediation reassessment of findings **F01–F39** after local audit program completion and Wave 7 merge prep. Supersedes [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md) for code posture; links [remediation-tracker.md](remediation-tracker.md) and [merge-readiness-checklist.md](merge-readiness-checklist.md).

---

## Limitation banner

| Scope | Detail |
|-------|--------|
| **Code state** | **Merged to `main`** at `95bcd563` (PR #136 + #144, 2026-07-03). |
| **CI on `main`** | Post-merge inventory **5 / 68** gated workflows green (2026-07-03); **43 push workflows queued** on first merge wave (runs `28585705xxx`). Pre-merge baseline was 13/68. |
| **Main CI** | [28585705582](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705582) queued on `95bcd563`. |
| **Local gates** | All merge-gate commands below passed on working tree (2026-07-03). |
| **68/68 sign-off** | **Not claimed.** Requires two consecutive `ci_workflow_inventory.sh` exit 0 on `main`. |

---

## Executive delta (v1 → v2)

| Metric | 2026-07-02 reassessment | 2026-07-03 v2 |
|--------|-------------------------|---------------|
| Findings DONE | 32 | **36** |
| Findings PARTIAL | 6 | **3** (F23, F24, F33 root Policy + MicroInterp) |
| Findings OPEN | 1 (F38) | **0** |
| Gated workflows green on `main` | 13 / 68 | **5 / 68** post-merge snapshot (43 queued); refresh after wave completes |
| Sidecar production unwrap/expect | 40 | **0** (`--max 10`) |
| Ledger `any` | 76 | **0** (`--max 20`) |
| CI honesty unjustified | 59 | **0** (56 justified) |
| Invariants.lean `sorry` | 7 | **0** |
| Out-of-scope Lean sorry | 15 | **6** (root Policy + MicroInterp) |
| CI-enforced Lean targets | 5 paths | **6 paths** (+ `Invariants.lean`, 2026-07-03) |

---

## Verification commands (2026-07-03)

| Command | Exit | Output summary |
|---------|------|----------------|
| `python scripts/count_sidecar_unwraps.py --max 10` | **0** | 0 production unwrap/expect |
| `python scripts/count_ledger_any.py --max 20` | **0** | 0 `any` |
| `python scripts/audit_ci_honesty.py` | **0** | 56 justified, 0 unjustified |
| `cargo test -p retrieval-gateway` | **0** | 14 passed |
| `PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests` | **0** | 9 passed |
| `cd runtime/ledger && npm test` | **0** | 23 passed, 1 skipped |
| `cd runtime/ledger && npm run typecheck:server` | **0** | clean |
| `python tests/crypto/test_cross_lang_dsse.py` | **0** | cross-lang DSSE |
| `make docs-strict` | **0** | mkdocs strict |
| `tests/replay/test_docker_invocation.sh` | skip/win | Docker required; wired in CI |
| `bash scripts/linux_validation_checklist.sh` | partial/win | All non-Docker steps pass on Windows |
| `scripts/ci_workflow_inventory.ps1 -Markdown` | **1** | 5/68 green on `main` post-merge (`95bcd563`); 43 workflows queued |

---

## Findings summary

### DONE locally (36) — main CI proof pending merge

F01–F22, F25–F32, F34–F39. Trust chain, ledger/MCP, sidecar burn-down, CI honesty, demos, ESLint 9, retention SQL guard, retrieval-gateway, compose profiles.

### PARTIAL (3)

| ID | Local | Remaining for DONE |
|----|-------|-------------------|
| **F23** | `bench-nightly-criterion.yaml` + `refresh_baseline` documented | Dispatch on `main`, commit baseline, two green runs |
| **F24** | `integration_tests` 9/9 + rate-limit cluster; `PF_SHADOW_MODE=1` in workflows | Two green `paper-conformance.yaml` on `main` |
| **F33** | `Invariants.lean` **0 sorry** + **CI-enforced**; `proofs/Policy.lean` **0 sorry** | Consolidate root `Policy.lean` (4 sorry); prove MicroInterp (2) |

#### F33 — Invariants enforced-set expansion (2026-07-03)

`core/lean-libs/Invariants.lean` is now in the `lean-style.yaml` **ENFORCED** list alongside ActionDSL, Budget, and bundle specs. The workflow step **Check for 'sorry' or 'by admit' in CI-enforced Lean targets** will fail if any placeholder is reintroduced in Invariants. Existing enforced targets were not weakened. See [lean-sorry-burn-down.md](lean-sorry-burn-down.md).

### OPEN (0)

F38 ESLint 9 migration complete (root flat config + packages).

---

## Production hardening — CI wiring (Phase D)

| ID | Hardening | Wired in CI | Main proof |
|----|-----------|-------------|------------|
| F01 | `PF_ENFORCE_DSSE=1` | `reusable-ci-extended.yml` → `test_cross_lang_dsse.py` | Main run pending [28585705582](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705582) queued |
| F02 | Deny-by-default `PF_ENABLED_TOOLS=` | `env_config::enabled_tools_deny_by_default` in `sidecar-watcher --lib` tests (`reusable-ci-rust.yml`) + compose `PF_ENABLED_TOOLS=` | Main CI queued |
| F03/F04 | MCP tenant | `integration.yaml` → `test_ledger_mcp_tenant.py` | [28585706085](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085) queued |
| F05 | retrieval-gateway | `retrieval-gateway.yml` | [28585706166](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706166) queued |
| F21 | Compose smoke | `integration.yaml` → `docker-compose-smoke.sh` | [28585706085](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085) queued |

---

## Wave 7 execution log (2026-07-03, session 3 — post-merge)

| Todo | Status | Evidence |
|------|--------|----------|
| phase0-merge-pr144 | **DONE** | Merged `95bcd563` (PR #136 + #144) to `main` |
| phase1-replay-security | **IN PROGRESS** | 43 post-merge runs queued (`28585705xxx`); cluster helper all `no_run`/pending |
| phase1-platform-lean | **IN PROGRESS** | `integration.yaml` [28585706085](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085), `paper-conformance.yaml` [28585705694](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705694) queued |
| phase1-bench-docs | **IN PROGRESS** | `docs-build.yaml` [28585705338](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705338) queued; Criterion [28585900934](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585900934) queued |
| phase1-remaining-workflows | **IN PROGRESS** | Inventory **5/68** honest snapshot; refresh after queue drains |
| phase2-f33-policy | **PARTIAL** | `proofs/Policy.lean` 0 sorry; root `Policy.lean` 4 sorry; `MicroInterp.lean` 2 sorry |
| phase3-hardening-proof | **IN PROGRESS** | F01/F03-F05/F21 runs queued on `95bcd563`; no conclusions yet |
| phase4-signoff | **IN PROGRESS** | Docs + inventory refreshed; 68/68 **not claimed** |

### Wave 7 execution log (2026-07-03, session 2 — superseded)

| Todo | Status | Evidence |
|------|--------|----------|
| phase0-merge-pr144 | **DONE** | Superseded by session 3 merge |
| phase1-replay-security | **NOT STARTED (main)** | PR-only green: `replay-tests`, `deny` [28582134163](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28582134163); post-merge cluster proof blocked on merge |
| phase1-platform-lean | **NOT STARTED (main)** | `Invariants.lean` ENFORCED; `integration` compose smoke fix `05d9cd6a`; re-run [28583016953](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28583016953) queued |
| phase1-bench-docs | **NOT STARTED (main)** | `Documentation Build` PR green [28582134001](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28582134001); Criterion baseline refresh not dispatched on `main` |
| phase1-remaining-workflows | **NOT STARTED** | `main` 13/68; inventory refresh deferred until merge |
| phase2-f33-policy | **PARTIAL** | `proofs/Policy.lean` 0 sorry; root `Policy.lean` 4 sorry; `MicroInterp.lean` 2 sorry |
| phase3-hardening-proof | **WIRED ONLY** | F01/F03-F05/F21 in workflows; no `main` CI run IDs |
| phase4-signoff | **IN PROGRESS** | Docs updated with PR run IDs; 68/68 **not claimed** |

---

## Wave 7 path (post-merge)

| Milestone | Target | Clusters |
|-----------|-------:|----------|
| M0 | Merge PR-M0 | Linux checklist on PR |
| M1 | ~20/68 | Replay + Security |
| M2 | ~25/68 | + Lean (paper-conformance) |
| M3 | ~35/68 | + Platform |
| M4 | ~50/68 | + Bench + Docs |
| M5 | 68/68 | Remaining ~30 |

Runbook: [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md). Cluster helper: `bash scripts/wave7_cluster_status.sh`.

---

## Honest bottom line

**Code remediation merged to `main` (`95bcd563`).** Wave 7 Phase 1 is **in progress**: post-merge inventory reports **5/68** green with **43 workflows queued** on the first push wave. Cluster proof (replay, security, platform, lean, bench) awaits run conclusions — main CI [28585705582](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705582) still queued. **PR #143** (dependabot docs) rebased; CI [28586333806](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28586333806) pending — merge blocked until **CI required checks**, **smoke**, **evidence-schema-only**, **Documentation Build** green. **PR #138** remains **CONFLICTING** with `main`. Do not publish 68/68 or full evidence-program sign-off until inventory ceremony passes on `main` twice.

---

## References

- [remediation-tracker.md](remediation-tracker.md)
- [merge-readiness-checklist.md](merge-readiness-checklist.md)
- [merge-pr-body.md](merge-pr-body.md)
- [ci-inventory-latest.md](ci-inventory-latest.md)
- [evidence-program-closure.md](../roadmap/evidence-program-closure.md)
- Prior: [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md)
