# Full Repository Audit — Reassessment Report v2 (2026-07-03)

Post-remediation reassessment of findings **F01–F39** after local audit program completion and Wave 7 merge prep. Supersedes [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md) for code posture; links [remediation-tracker.md](remediation-tracker.md) and [merge-readiness-checklist.md](merge-readiness-checklist.md).

---

## Limitation banner

| Scope | Detail |
|-------|--------|
| **Code state** | Wave 8 tip `6b99ef300` (#215–#221); F33 MicroInterp **0** sorry (2026-07-18). |
| **CI on `main`** | Inventory **69** gated (Wave 8 re-gates); exit **0 ×2** @ tip (2026-07-18T15:02Z / 15:04Z UTC). Do **not** claim literal 67/67. |
| **Main CI** | Tip CI green [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623) on historical `b8b78b94`; Wave 8 tip `6b99ef300`; `lean-offline-full` [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851). |
| **Local gates** | All merge-gate commands below passed on working tree (2026-07-03); burn-down gates unchanged. |
| **69/69 sign-off** | **Claimed** for gated set after Wave 8 (inventory ×2 @ `6b99ef300`). Literal 67/67 **not claimed**. Live AWS DR / multi-region SaaS / live publish / live revocation remain secret/live-mode only. |

---

## Executive delta (v1 → v2)

| Metric | 2026-07-02 reassessment | 2026-07-03 v2 |
|--------|-------------------------|---------------|
| Findings DONE | 32 | **39** (F23/F24 closed 2026-07-16; F33 MicroInterp closed 2026-07-18) |
| Findings PARTIAL | 6 | **0** |
| Findings OPEN | 1 (F38) | **0** |
| Gated workflows green on `main` | 13 / 68 | **69** gated after Wave 8 re-gates (#215–#217) |
| Sidecar production unwrap/expect | 40 | **0** (`--max 10`) |
| Ledger `any` | 76 | **0** (`--max 20`) |
| CI honesty unjustified | 59 | **0** (56 justified) |
| Invariants.lean `sorry` | 7 | **0** |
| Out-of-scope Lean sorry (F33 set) | 15 | **0** (Policy trees + MicroInterp closed) |
| CI-enforced Lean targets | 5 paths | **6 paths** (+ `Invariants.lean`, 2026-07-03); MicroInterp scanned by lean-offline smoke |

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

### DONE (39) — including main CI proof

F01–F39. Trust chain, ledger/MCP, sidecar burn-down, CI honesty, demos, ESLint 9, retention SQL guard, retrieval-gateway, compose profiles, F23 Criterion, F24 paper-conformance, **F33 Lean sorry debt** (Invariants + both Policy trees + MicroInterp **0** sorry; Runtime lake target; lean-style ENFORCED not weakened).

### PARTIAL (0)

None. F33 closed 2026-07-18 (PR #215): `dfa_semantics_match` proved; see [lean-sorry-burn-down.md](lean-sorry-burn-down.md).

#### F33 — closed (2026-07-18)

`core/lean-libs/Invariants.lean` remains in the `lean-style.yaml` **ENFORCED** list. MicroInterp is lake-built and scanned by `lean-offline` smoke; do **not** add it to lean-style ENFORCED until an Extended.Event adapter exists. Existing enforced targets were not weakened.

### OPEN (0)

F38 ESLint 9 migration complete (root flat config + packages).

---

## Production hardening — CI proof (Phase D / Phase 3) — **DONE**

| ID | Hardening | Wired in CI | Main proof |
|----|-----------|-------------|------------|
| F01 | Cross-lang DSSE | `ci.yml` → `reusable-ci-extended.yml` → `test_cross_lang_dsse.py` | [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623) (`b8b78b94`); [29529736631](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29529736631) (`7d48b3d4`) |
| F02 | Deny-by-default `PF_ENABLED_TOOLS=` | Compose `PF_ENABLED_TOOLS=` in F21 smoke; in-tree `enabled_tools_deny_by_default` (not in curated `reusable-ci-rust` `--lib`) | [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F03/F04 | MCP tenant | `integration.yaml` → `test_ledger_mcp_tenant.py` | [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F05 | retrieval-gateway | `retrieval-gateway.yml` | [29410389588](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588); [28639549745](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549745) |
| F21 | Compose smoke | `integration.yaml` → `docker-compose-smoke.sh full` | Same integration runs as F03/F04 |

---

## Wave 7 execution log (2026-07-03, session 3 — post-merge)

| Todo | Status | Evidence |
|------|--------|----------|
| phase0-merge-pr144 | **DONE** | Merged `95bcd563` (PR #136 + #144) to `main` |
| phase1-replay-security | **IN PROGRESS** | 43 post-merge runs queued (`28585705xxx`); cluster helper all `no_run`/pending |
| phase1-platform-lean | **IN PROGRESS** | `integration.yaml` [28585706085](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085), `paper-conformance.yaml` [28585705694](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705694) queued |
| phase1-bench-docs | **IN PROGRESS** | `docs-build.yaml` [28585705338](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705338) queued; Criterion [28585900934](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585900934) queued |
| phase1-remaining-workflows | **IN PROGRESS** | Inventory **5/68** honest snapshot; refresh after queue drains |
| phase2-f33-policy | **DONE** | F33 closed 2026-07-18: MicroInterp **0** sorry + Runtime lake; Policy trees **0**; PR #215 |
| phase3-hardening-proof | **DONE** | F01/F02/F03–F05/F21 proven on `main` with run IDs (Phase D table); tip `b8b78b94` |
| phase4-signoff | **DONE** | Inventory **60/60** exit 0 ×2; F23/F24 DONE; ungated list recorded; literal 67/67 **not claimed** |

### Wave 7 execution log (2026-07-03, session 2 — superseded)

| Todo | Status | Evidence |
|------|--------|----------|
| phase0-merge-pr144 | **DONE** | Superseded by session 3 merge |
| phase1-replay-security | **NOT STARTED (main)** | PR-only green: `replay-tests`, `deny` [28582134163](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28582134163); post-merge cluster proof blocked on merge |
| phase1-platform-lean | **NOT STARTED (main)** | `Invariants.lean` ENFORCED; `integration` compose smoke fix `05d9cd6a`; re-run [28583016953](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28583016953) queued |
| phase1-bench-docs | **NOT STARTED (main)** | `Documentation Build` PR green [28582134001](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28582134001); Criterion baseline refresh not dispatched on `main` |
| phase1-remaining-workflows | **NOT STARTED** | `main` 13/68; inventory refresh deferred until merge |
| phase2-f33-policy | **DONE** | F33 closed 2026-07-18: MicroInterp **0** sorry + Runtime lake; Policy trees **0**; PR #215 |
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
| M5 | 60/60 (exit 0) | **DONE** — honest ungates; not literal 67/67 |

Runbook: [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md). Cluster helper: `bash scripts/wave7_cluster_status.sh`.

---

## Honest bottom line

**Wave 7 Phase 3+4 complete (2026-07-16).** Historical tip `b8b78b94`. Inventory **60/60** gated green, exit **0 ×2**. F23/F24 **DONE**. Phase 3 hardening (F01–F05, F21) proven with main run IDs. **Wave 8 (2026-07-18):** F33 **DONE** (MicroInterp 0 sorry); 8 leftovers re-gated; `lean-offline-full` proven [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851); tip `6b99ef300`; inventory **69** gated, exit **0 ×2**. Live-only deferred: live AWS DR, multi-region SaaS load, live registry publish, live revocation sync. Literal **67/67 is not claimed**.

---

## References

- [remediation-tracker.md](remediation-tracker.md)
- [merge-readiness-checklist.md](merge-readiness-checklist.md)
- [merge-pr-body.md](merge-pr-body.md)
- [ci-inventory-latest.md](ci-inventory-latest.md)
- [evidence-program-closure.md](../roadmap/evidence-program-closure.md)
- Prior: [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md)
