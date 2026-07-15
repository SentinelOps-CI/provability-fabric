# Audit Remediation Tracker

Maps findings **F01–F39** from [full-repo-audit-2026-07-01.md](full-repo-audit-2026-07-01.md) to remediation waves, status, burn-down IDs, and CI proof. Established during **Wave 0** reconciliation (2026-07-01). Last verified against code: **2026-07-15** (main @ `ee68659c`).

**Reassessment v2:** [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md)

**North-star:** 69/69 gated workflows green with honest gates; trust chain fail-closed; burn-down reflects code reality.

---

## CI baseline (Wave 0 inventory)

Captured via `powershell -File scripts/ci_workflow_inventory.ps1 -Markdown` (2026-07-15; requires `gh` CLI authenticated to repo). Full table: [ci-inventory-latest.md](ci-inventory-latest.md).

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on `main`) | 69 |
| Latest run **success** | 38 |
| Latest run **failure / in_progress / cancelled** | 31 |
| No run / unknown (queued) | 18 |

**Green snapshot (38/69, 2026-07-15):** replay cluster, security baseline (`cargo-deny`, `scorecards`, `wasm-scan`), `integration.yaml` ([28639549743](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549743)), `retrieval-gateway.yml`, `proto-compat.yaml`, `privacy-test.yaml`, `proof-bot.yaml`, and related scheduled/nightly lanes — see inventory for full list.

**No run on main (gated):** `policy-build.yml`, `release.yaml`, `verify-publish-bundle.yaml` (awaiting trigger).

Re-run: `scripts/ci_workflow_inventory.sh` (Linux/WSL/Git Bash) or `powershell -File scripts/ci_workflow_inventory.ps1` (Windows).

**Note:** **PR #136 + #144 merged** to `main` at `95bcd563` (2026-07-03). **PR #146 merged** 2026-07-02 (wasm-scan, retrieval-gateway Docker, CodeQL). **PR #151 merged** at `ee68659c` (2026-07-03, F21 compose postgres init). Post-merge honest inventory **38/69** green (2026-07-15); integration F10+F21 green on `main`. Active cluster fixes: paper-conformance scheduler ([PR #163](https://github.com/SentinelOps-CI/provability-fabric/pull/163)), multiarch native musl ([PR #164](https://github.com/SentinelOps-CI/provability-fabric/pull/164)). Wave 7 cluster triage: [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md).

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
| F01 | P0 | Signature verification stubbed (Go/Rust/TS) | 2 | **DONE** | ST-005, TD-001, TD-003–TD-005, TD-008, PH-004 | — | `tests/crypto/test_cross_lang_dsse.py`; `PF_ENFORCE_DSSE=1` documented in deployment-guide + compose `full` profile |
| F02 | P0 | Shadow mode always allows; `is_tool_enabled` always true | 2 | **DONE** | PH-004, PH-005 | — | `env_config.rs`: deny-by-default `PF_ENABLED_TOOLS`; documented in deployment-guide + compose |
| F03 | P0 | Ledger Docker runs `index-simple.js`; MCP only in `index.ts` | 4 | **DONE** | — | — | `runtime/ledger/Dockerfile` CMD → `dist/index.js`; `tests/integration/test_ledger_mcp_tenant.py` |
| F04 | P0 | MCP tenant field mismatch (`tid` vs `tenant_id`) | 4 | **DONE** | TD-006 | — | `mcp-proxy.ts` + `mcp-service.ts` + integration test |
| F05 | P0 | `retrieval-gateway` unbuildable | 5 | **DONE** | PH-006 | — | `cargo build/test -p retrieval-gateway`; `.github/workflows/retrieval-gateway.yml` |
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
| F21 | P1 | Runtime components absent from compose | 5 | **DONE** | — | — | `docker-compose.yml` profiles + `scripts/docker-compose-smoke.sh` |
| F22 | P1 | `ws` missing from ledger | 4 | **DONE** | — | — | `package.json`; `mcp-websocket.test.cjs` smoke stub |
| F23 | P1 | Bench Nightly Criterion regression | 1 | **PARTIAL** | — | — | `bench-nightly-criterion.yaml` `refresh_baseline` input; `bench/BASELINE.md`; needs main CI refresh |
| F24 | P1 | Paper Conformance sidecar integration failures | 1, 3 | **PARTIAL** | — | — | Local: `integration_tests` (9/9) + rate-limit cluster (`test_rate_limiter_basic`, `test_optimized_rate_limiter`, `test_99th_percentile_performance`, `test_clock_wraparound_safety`, `test_monotonicity_guarantee`) in `paper-conformance.yaml`; `Instant` overflow + ε-tolerance fixed in `ratelimit.rs`; `PF_SHADOW_MODE=1` on integration + rate-limits jobs and `reusable-ci-rust.yml`; needs **two** green `paper-conformance.yaml` on `main` |
| F25 | P1 | Egress cert evidence hardcoded accept | 2 | **DONE** | PH-005 | — | `env_config::resolve_evidence_hash`; `egress_evidence_enforcement.rs` |
| F26 | P2 | Duplicate ledger entrypoints | 4 | **DONE** | — | — | `index-simple.ts` / `index-production.ts` removed; single `index.ts` + PROFILE env |
| F27 | P2 | 152 `any` in ledger src | 4 | **DONE** | — | — | `scripts/count_ledger_any.py --max 20` (0 `any`); `tsconfig.server.json` strict on server/mcp/receipts/egress |
| F28 | P2 | Dual Apollo server stack | 4 | **DONE** | — | — | `apollo-server-express` removed; `@apollo/server` v4 only; `wave4.test.cjs` |
| F29 | P2 | Duplicate `epsilon_guard.rs` | 5 | **DONE** | — | — | Single copy in sidecar |
| F30 | P2 | Egress-firewall regex recompiled per call | 3 | **DONE** | — | — | `lazy_static!` cached regexes |
| F31 | P2 | MD5 for approval token IDs | 3 | **DONE** | — | — | UUID in tool-broker |
| F32 | P2 | Documentation drift | 5 | **DONE** | — | — | `make docs-strict` green (2026-07-02 local) |
| F33 | P2 | Lean sorry debt | 6 | **PARTIAL** | LN-* | — | [lean-sorry-burn-down.md](lean-sorry-burn-down.md): Invariants.lean **0 sorry** + **CI-enforced** (2026-07-03 Wave 7); `proofs/Policy.lean` **4→0** sorry; root `Policy.lean` **4** + MicroInterp **2** remain |
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
| 1 | CI unblock and honesty | F06, F10–F12, F19–F24 | Replay green; ≥25/67 workflows green | **IN PROGRESS** — Phase 0 local prep done; Phase 1 cluster prep landed (honesty gate in `ci.yml`, `integration_tests` in reusable Rust CI, `PF_SHADOW_MODE` in paper-conformance); main CI proof pending merge |
| 2 | Trust chain core | F01–F02, F17, F25 | Cross-lang DSSE; fail-closed when enforced | **DONE** |
| 3 | Runtime hardening + sidecar CI | F13–F16, F30–F31, F35 | Sidecar in PR CI | **DONE** |
| 4 | Ledger + MCP consolidation | F03–F04, F09, F11, F22, F26–F28 | Docker MCP + Jest suite | **DONE** |
| 5 | Architecture, demos, topology | F05, F07–F08, F18, F21, F29, F32, F34 | Demos/examples pass | **DONE** |
| 6 | Quality, docs, formal methods | F33, F37–F39 | mkdocs strict; Lean enforced targets | **MOSTLY DONE** — F33 partial (Invariants **0** sorry + enforced; `proofs/Policy.lean` **0** sorry; root Policy + MicroInterp **6** remain); F38 done |
| 7 | CI green program | All CI clusters | 69/69 gated green twice on main | **IN PROGRESS** — `ee68659c` on `main`; inventory **38/69** green (2026-07-15); PR #146 merged; integration F10+F21 green; paper-conformance + multiarch fixes in flight (#163, #164) |

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
| Criterion `refresh_baseline` | **DOCUMENTED** | `bench/BASELINE.md` + `bench-nightly-criterion.yaml` `workflow_dispatch` input |

**Still pending main CI proof:** paper-conformance + multiarch clusters (PRs #163/#164), bench baseline refresh (F23), 69/69 inventory ×2. Main @ `ee68659c`; integration green — see [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md).

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
