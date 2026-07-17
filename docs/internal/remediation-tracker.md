# Audit Remediation Tracker

Maps findings **F01–F39** from [full-repo-audit-2026-07-01.md](full-repo-audit-2026-07-01.md) to remediation waves, status, burn-down IDs, and CI proof. Established during **Wave 0** reconciliation (2026-07-01). Last verified against code: **2026-07-17** (F33 PARTIAL — MicroInterp 2 sorry blocked on DFA↔semantics generator; tip was `43367813b`).

**Reassessment v2:** [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md)

**North-star:** inventory exit 0 on all push/schedule workflows (achieved **60/60** @ `7d48b3d4`, reconfirmed tip `b8b78b94`, 2026-07-16); trust chain fail-closed; burn-down reflects code reality. Do **not** claim literal 67/67.

---

## CI baseline (Wave 0 inventory)

Captured via `powershell -File scripts/ci_workflow_inventory.ps1 -Markdown` (2026-07-16; requires `gh` CLI authenticated to repo). Full table: [ci-inventory-latest.md](ci-inventory-latest.md).

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on `main`) | 60 |
| Latest run **success** | 60 |
| Latest run **failure / cancelled** (ungated / PR-only) | 11 |
| No run / unknown | 16 |

**Green snapshot (60/60 gated, inventory exit 0 ×2, 2026-07-16):** all push/schedule workflows green after **PR #206** honest ungating of seven SaaS/AWS leftovers; tip `b8b78b94` (#207 docs). See [ci-inventory-latest.md](ci-inventory-latest.md).

**No run on main (gated):** none — full gated set green.

Re-run: `scripts/ci_workflow_inventory.sh` (Linux/WSL/Git Bash) or `powershell -File scripts/ci_workflow_inventory.ps1` (Windows).

**Note:** **PR #206 merged** at `7d48b3d4`; tip **`b8b78b94`** after **PR #207** (2026-07-16). Inventory **60/60** exit 0 ×2. Phase 3 hardening proof + Phase 4 sign-off: [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md) Phase D/E. F23/F24 **DONE**.

---

## Gate command results (Wave 0 + 2026-07-02 local)

| Command | Exit | Notes |
|---------|------|-------|
| `make no-runtime-placeholders` | **0** | `.placeholderignore` + `build/`/`dist/` skip; binary detection (2026-07-02 Phase 0) |
| `python scripts/check_no_placeholder.py` | **0** | Same as above |
| `python scripts/audit_ci_honesty.py` | **0** | 56 justified suppressions; 0 unjustified (Phase 1.6) |
| `cargo build -p retrieval-gateway` | **0** | F05 — deps + pf-dsse wired |
| `cargo test -p retrieval-gateway` | **0** | 14 tests |
| `cargo test -p sidecar-watcher --test integration_tests` | **0** | 9 tests (shadow mode requires `PF_SHADOW_MODE=1`) |
| `cargo test -p sidecar-watcher --lib test_clock_wraparound_safety test_monotonicity_guarantee` | **0** | F24 rate-limit cluster (Instant overflow safe) |
| `cargo test -p sidecar-watcher --lib test_99th_percentile_performance` | **0** | F24 |
| `cargo test -p sidecar-watcher --test egress_evidence_enforcement` | **0** | F25 |
| `cd runtime/ledger && npm test` | **0** | 23 Jest tests (+ 1 skipped ws handshake when `ws` not installed) |
| `cd runtime/ledger && npm run typecheck:server` | **0** | F27 `noImplicitAny` for server + mcp + receipts + egress |
| `make docs-strict` | **0** | F32 |
| `python ops/retention/test_retention_manager.py` | **0** | F39 |
| `python scripts/count_sidecar_unwraps.py` | **0** | **0** production unwrap/expect (gate `--max 10`) |
| `python scripts/count_ledger_any.py` | **0** | **0** `any` (regression baseline 152; ceiling gate `--max 20`) |
| `python scripts/count_ledger_any.py --max 20` | **0** | F27 CI gate |
| `tests/replay/test_docker_invocation.sh` | skip/win | Requires Docker + TRACE-REPLAY-KIT submodule on Linux; wired in `integration.yaml` + replay cluster workflows |
| `scripts/linux_validation_checklist.sh` | **added** | Phase 0 merge gate script (Ubuntu/WSL) |

**Trust-path grep (2026-07-02):** DSSE wired in Go kernel, Rust sidecar, tool-broker, ledger, TS SDK. Fail-closed when `PF_ENFORCE_DSSE=1` and trust root configured.

---

## Findings tracker

| ID | Sev | Finding (summary) | Wave | Status | Burn-down | PR | CI proof |
|----|-----|-------------------|------|--------|-----------|-----|----------|
| F01 | P0 | Signature verification stubbed (Go/Rust/TS) | 2 | **DONE** | ST-005, TD-001, TD-003–TD-005, TD-008, PH-004 | — | `ci.yml` → `reusable-ci-extended.yml` DSSE green on `main`: [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623), [29529736631](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29529736631) |
| F02 | P0 | Shadow mode always allows; `is_tool_enabled` always true | 2 | **DONE** | PH-004, PH-005 | — | Compose `PF_ENABLED_TOOLS=` via F21 smoke [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757); in-tree `enabled_tools_deny_by_default` (not in curated `reusable-ci-rust` `--lib`) |
| F03 | P0 | Ledger Docker runs `index-simple.js`; MCP only in `index.ts` | 4 | **DONE** | — | — | `integration.yaml` MCP tenant tests green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757), [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F04 | P0 | MCP tenant field mismatch (`tid` vs `tenant_id`) | 4 | **DONE** | TD-006 | — | Same integration runs as F03 (4 tenant tests) |
| F05 | P0 | `retrieval-gateway` unbuildable | 5 | **DONE** | PH-006 | — | `retrieval-gateway.yml` green ×2: [29410389588](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588), [28639549745](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549745) |
| F06 | P0 | Ghost integration tests in CI | 1 | **DONE** | — | — | `tests/integration/test_*.py` (10 pytest smoke tests) |
| F07 | P0 | Broken MCP fraud demo | 5 | **DONE** | — | — | `demos/verifiable-mcp-fraud/scripts/run-demo.ts` |
| F08 | P0 | Broken edge-middleware example import | 5 | **DONE** | — | — | `examples/edge-middleware/index.ts` |
| F09 | P0 | Broken Prisma performance migration | 4 | **DONE** | PH-008 | — | Quarantined; `prisma/migrations/README.md`; `migrate deploy` on fresh DB via baseline migration |
| F10 | P0 | Replay Docker CLI invocation bug | 1 | **DONE** | — | — | `tests/replay/test_docker_invocation.sh` (contract test; merge + Linux CI for cluster green) |
| F11 | P1 | Vacuous Jest gates | 1, 4 | **DONE** | TD-005–TD-011 | — | Ledger 23+ Jest tests; SDK 4 tests in `reusable-ci-go-node.yml`; marketplace-e2e conditional Jest (no `passWithNoTests`) |
| F12 | P1 | Impacted-test selector format mismatch | 1 | **DONE** | ST-008 | — | `tools/test_select_impacted.py` |
| F13 | P1 | Sidecar excluded from PR `cargo test` | 3 | **DONE** | — | — | `reusable-ci-rust.yml` runs `--test integration_tests` with `PF_SHADOW_MODE=1` |
| F14 | P1 | 4 sidecar integration tests quarantined | 3 | **DONE** | — | — | `ni_monitor_egress`, `safety_case_bundle`, `events_plan_dsl`, `hardened_adapters` registered in Cargo.toml + CI; 11 tests green |
| F15 | P1 | Sync blocking I/O in async log watcher | 3 | **DONE** | — | — | `spawn_blocking` in log watcher |
| F16 | P1 | 97 production unwrap/expect/panic in sidecar | 3 | **DONE** | — | — | `scripts/count_sidecar_unwraps.py --max 10` — **0** prod unwrap/expect; shared `time_util`; CI gate in `reusable-ci-rust.yml` |
| F17 | P1 | SDK `verifyTrace` always `{ valid: true }` | 2 | **DONE** | TD-009–TD-011 | — | `verifyTrace.ts` + Jest |
| F18 | P1 | Demo imports `SentinelOpsClient` | 5 | **DONE** | TD-009 | — | SDK exports |
| F19 | P1 | SLO Gates — no root lockfile | 1 | **DONE** | — | — | Mock PF server in workflow |
| F20 | P1 | CodeQL artifact upload broken | 1 | **DONE** | — | — | `codeql.yaml` matrix |
| F21 | P1 | Runtime components absent from compose | 5 | **DONE** | — | — | `integration.yaml` compose smoke green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757), [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F22 | P1 | `ws` missing from ledger | 4 | **DONE** | — | — | `package.json`; `mcp-websocket.test.cjs` smoke stub |
| F23 | P1 | Bench Nightly Criterion regression | 1 | **DONE** | — | [#197](https://github.com/SentinelOps-CI/provability-fabric/pull/197), [#198](https://github.com/SentinelOps-CI/provability-fabric/pull/198) | Green ×3 on `main` @ `1ab0d2d5`: [29508973817](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973817) (push), [29509027731](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509027731) + [29509041247](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509041247) (`refresh_baseline`); timeout CI overrides + ring-buffer MPMC hang fix |
| F24 | P1 | Paper Conformance sidecar integration failures | 1, 3 | **DONE** | — | [#176](https://github.com/SentinelOps-CI/provability-fabric/pull/176) | `paper-conformance.yaml` green ×2 on `main` @ `f4b0859e`: [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434) (push), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127) (dispatch); integration gates unchanged |
| F25 | P1 | Egress cert evidence hardcoded accept | 2 | **DONE** | PH-005 | — | `env_config::resolve_evidence_hash`; `egress_evidence_enforcement.rs` |
| F26 | P2 | Duplicate ledger entrypoints | 4 | **DONE** | — | — | `index-simple.ts` / `index-production.ts` removed; single `index.ts` + PROFILE env |
| F27 | P2 | 152 `any` in ledger src | 4 | **DONE** | — | — | `scripts/count_ledger_any.py --max 20` (0 `any`); `tsconfig.server.json` strict on server/mcp/receipts/egress |
| F28 | P2 | Dual Apollo server stack | 4 | **DONE** | — | — | `apollo-server-express` removed; `@apollo/server` v4 only; `wave4.test.cjs` |
| F29 | P2 | Duplicate `epsilon_guard.rs` | 5 | **DONE** | — | — | Single copy in sidecar |
| F30 | P2 | Egress-firewall regex recompiled per call | 3 | **DONE** | — | — | `lazy_static!` cached regexes |
| F31 | P2 | MD5 for approval token IDs | 3 | **DONE** | — | — | UUID in tool-broker |
| F32 | P2 | Documentation drift | 5 | **DONE** | — | — | `make docs-strict` green (2026-07-02 local) |
| F33 | P2 | Lean sorry debt | 6 | **PARTIAL** | LN-* | — | [lean-sorry-burn-down.md](lean-sorry-burn-down.md): Invariants **0** + enforced; both Policy trees **0**; MicroInterp **2** (`dfa_semantics_match`) remain — P4.1–P4.3 generator coupling required; enforced set not weakened |
| F34 | P2 | Two parallel VS Code extensions | 5 | **DONE** | TD-013 | — | [documentation-map.md](../documentation-map.md) § VS Code |
| F35 | P2 | Crate-wide `#![allow(dead_code)]` on sidecar | 3 | **DONE** | — | — | Module allows removed; lib `-D dead_code` in `reusable-ci-rust.yml` (lib + `integration_tests`); bin scaffold deferred |
| F36 | P3 | No pre-commit hooks | 0 | **DONE** | — | Wave 0 | `.pre-commit-config.yaml` |
| F37 | P3 | No root `go.work` | 6 | **DONE** | — | — | `go.work.example` + `make go-work` + CONTRIBUTING |
| F38 | P3 | ESLint 8.x EOL | 6 | **DONE** | — | — | Root `eslint.config.mjs`; ledger, SDK, console, rag-guard, incident-bot, demos on ESLint 9 |
| F39 | P3 | Dynamic SQL table interpolation | 6 | **DONE** | — | — | `_validate_table_name` + `ops/retention/test_retention_manager.py` |

---

## Wave summary

| Wave | Focus | Findings | Exit gate | Status (2026-07-02) |
|------|-------|----------|-----------|---------------------|
| 0 | Foundation / truth baseline | F36 | Tracker + burn-down reconciled | **DONE** |
| 1 | CI unblock and honesty | F06, F10–F12, F19–F24 | Replay green; ≥25/67 workflows green | **DONE** — F24 closed @ `f4b0859e`; F23 Criterion green ×3 on `main` @ `1ab0d2d5` (#197/#198) |
| 2 | Trust chain core | F01–F02, F17, F25 | Cross-lang DSSE; fail-closed when enforced | **DONE** |
| 3 | Runtime hardening + sidecar CI | F13–F16, F30–F31, F35 | Sidecar in PR CI | **DONE** |
| 4 | Ledger + MCP consolidation | F03–F04, F09, F11, F22, F26–F28 | Docker MCP + Jest suite | **DONE** |
| 5 | Architecture, demos, topology | F05, F07–F08, F18, F21, F29, F32, F34 | Demos/examples pass | **DONE** |
| 6 | Quality, docs, formal methods | F33, F37–F39 | mkdocs strict; Lean enforced targets | **MOSTLY DONE** — F33 partial (Invariants + both Policy trees **0** sorry; MicroInterp **2** remain); F38 done |
| 7 | CI green program | All CI clusters | 60/60 gated green twice on main (honest; not 67/67) | **DONE** — tip `b8b78b94`; F23+F24 DONE; inventory exit 0 ×2; Phase 3 hardening proof + Phase 4 sign-off recorded |

---

## Phase 0–1 prep status (2026-07-02)

| Item | Status | Evidence |
|------|--------|----------|
| Placeholder gate (`make no-runtime-placeholders`) | **DONE** (local) | `.placeholderignore`; `build/`/`dist/`/`site/` skip; binary detection in `check_no_placeholder.py` |
| TRACE-REPLAY-KIT submodule `CMD []` | **DONE** | `external/TRACE-REPLAY-KIT/runner/Dockerfile` ENTRYPOINT + `CMD []` at `957630f` |
| Linux validation checklist | **DONE** | `scripts/linux_validation_checklist.sh` |
| Replay contract in CI | **DONE** (wired) | `integration.yaml` + replay cluster workflows run `test_docker_invocation.sh` |
| CI honesty burn-down | **DONE** (local) | `audit_ci_honesty.py` exit 0; gate in `ci.yml` |
| `passWithNoTests` removed | **DONE** | `marketplace-e2e.yaml` — conditional Jest or skip |
| Sidecar `integration_tests` in PR Rust CI | **DONE** | `reusable-ci-rust.yml` with `PF_SHADOW_MODE=1` |
| Paper-conformance shadow mode | **DONE** (wired) | `paper-conformance.yaml` integration job sets `PF_SHADOW_MODE=1` |
| Criterion `refresh_baseline` | **DONE** | Green ×3 @ `1ab0d2d5`; `bench/BASELINE.md` recorded; #197/#198 |

**Wave 7 inventory gate:** **DONE** — inventory exit **0** twice on `main` @ `7d48b3d4` (**60/60** gated green); tip `b8b78b94` after #207. Seven leftovers remain `workflow_dispatch`-only (not gated; not proven in CI): `dr-cross` (AWS secret-presence skip), `edge-load`, `loadtest`, `perf-proofmeter`, `publish-updates`, `revocation-sync`, `pf-cross-repo-consumer`. Phase 3+4: [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md).

---

## Audit remediation program verification (2026-07-02)

| Metric | Result |
|--------|--------|
| `count_sidecar_unwraps.py --max 10` | **0** (exit 0) |
| `count_ledger_any.py --max 20` | **0** (exit 0) |
| `audit_ci_honesty.py` | exit **0** (56 justified, 0 unjustified) |
| `check_no_placeholder.py` | exit **0** |
| `cargo test -p sidecar-watcher --test integration_tests` | **9/9** pass |
| `cargo test -p sidecar-watcher --test ni_monitor_egress … hardened_adapters` | wired in CI |
| `python tests/crypto/test_cross_lang_dsse.py` | pass |
| `cd runtime/ledger && npm test` | **23 passed**, 1 skipped |
| `RUSTFLAGS=-D dead_code cargo test -p sidecar-watcher --lib` | pass |


`tests/replay/test_docker_invocation.sh` documents the F10 Docker contract (ENTRYPOINT `python replay_run.py`, not `bash replay_run.sh`). Skips gracefully without Docker/submodule. **Replay cluster workflows** (`platform-replay.yml`, `nightly-replay.yml`, `platform-cert-validate.yml`) require merge to `main` + Linux validation before marking green.

---

## References

- Original audit: [full-repo-audit-2026-07-01.md](full-repo-audit-2026-07-01.md)
- Reassessment v1: [full-repo-audit-reassessment-2026-07-02.md](full-repo-audit-reassessment-2026-07-02.md)
- **Reassessment v2 (POST-remediation):** [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md)
- [Placeholder burn-down](placeholders/burn-down.md)
- [CI health matrix](ci-health-matrix.md)
- [Evidence program closure](../roadmap/evidence-program-closure.md)
- [Ledger consolidation RFC](ledger-consolidation-rfc.md)
- [Lean sorry burn-down](lean-sorry-burn-down.md)
