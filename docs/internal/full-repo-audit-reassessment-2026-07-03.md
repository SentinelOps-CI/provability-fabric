# Full Repository Audit — Reassessment Report v2 (2026-07-03)

Post-remediation reassessment of findings **F01–F39** after local audit program completion and Wave 7 merge prep. Supersedes [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md) for code posture; links [remediation-tracker.md](remediation-tracker.md) and [merge-readiness-checklist.md](merge-readiness-checklist.md).

---

## Limitation banner

| Scope | Detail |
|-------|--------|
| **Code state** | Remediation on branch `audit-remediation-merge` — **not merged to `main`** until PR-M0 lands. |
| **CI on `main`** | **13 / 68** gated workflows green (inventory 2026-07-03); unchanged until merge. |
| **Local gates** | All merge-gate commands below passed on working tree (2026-07-03). |
| **67/67 sign-off** | **Not claimed.** Requires two consecutive `ci_workflow_inventory.sh` exit 0 on `main`. |

---

## Executive delta (v1 → v2)

| Metric | 2026-07-02 reassessment | 2026-07-03 v2 |
|--------|-------------------------|---------------|
| Findings DONE | 32 | **36** |
| Findings PARTIAL | 6 | **3** (F23, F24, F33 Policy tree) |
| Findings OPEN | 1 (F38) | **0** |
| Gated workflows green on `main` | 13 / 68 | **13 / 68** (pending merge) |
| Sidecar production unwrap/expect | 40 | **0** (`--max 10`) |
| Ledger `any` | 76 | **0** (`--max 20`) |
| CI honesty unjustified | 59 | **0** (56 justified) |
| Invariants.lean `sorry` | 7 | **0** |
| Out-of-scope Lean sorry | 15 | **10** (Policy + MicroInterp) |

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
| `scripts/ci_workflow_inventory.ps1 -Markdown` | **1** | 13/68 green on `main` |

---

## Findings summary

### DONE locally (36) — main CI proof pending merge

F01–F22, F25–F32, F34–F39. Trust chain, ledger/MCP, sidecar burn-down, CI honesty, demos, ESLint 9, retention SQL guard, retrieval-gateway, compose profiles.

### PARTIAL (3)

| ID | Local | Remaining for DONE |
|----|-------|-------------------|
| **F23** | `bench-nightly-criterion.yaml` + `refresh_baseline` documented | Dispatch on `main`, commit baseline, two green runs |
| **F24** | `integration_tests` 9/9 + rate-limit cluster; `PF_SHADOW_MODE=1` in workflows | Two green `paper-conformance.yaml` on `main` |
| **F33** | `Invariants.lean` **0 sorry**; Policy.lean trees still have 8 sorry | Prove `proofs/Policy.lean` (P2); expand enforced set when ready |

### OPEN (0)

F38 ESLint 9 migration complete (root flat config + packages).

---

## Production hardening — CI wiring (Phase D)

| ID | Hardening | Wired in CI | Main proof |
|----|-----------|-------------|------------|
| F01 | `PF_ENFORCE_DSSE=1` | `reusable-ci-extended.yml` → `test_cross_lang_dsse.py` | Pending merge |
| F02 | Deny-by-default `PF_ENABLED_TOOLS=` | `env_config` unit test + compose | Pending merge |
| F03/F04 | MCP tenant | `integration.yaml` → `test_ledger_mcp_tenant.py` | Pending merge |
| F05 | retrieval-gateway | `retrieval-gateway.yml` | No run on `main` yet |
| F21 | Compose smoke | `integration.yaml` → `docker-compose-smoke.sh` | Pending merge Linux CI |

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

**Code remediation is complete for merge.** The program bottleneck is **landing on `main` and proving CI clusters green twice** — not re-doing F16/F27/F38. Do not publish 67/67 or full evidence-program sign-off until inventory ceremony passes on `main`.

---

## References

- [remediation-tracker.md](remediation-tracker.md)
- [merge-readiness-checklist.md](merge-readiness-checklist.md)
- [merge-pr-body.md](merge-pr-body.md)
- [ci-inventory-latest.md](ci-inventory-latest.md)
- [evidence-program-closure.md](../roadmap/evidence-program-closure.md)
- Prior: [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md)
