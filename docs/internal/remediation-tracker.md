# Audit Remediation Tracker

Maps findings **F01â€“F39** from [full-repo-audit-2026-07-01.md](full-repo-audit-2026-07-01.md) to remediation waves, status, burn-down IDs, and CI proof. Established during **Wave 0** reconciliation (2026-07-01). Last verified against code: **2026-07-22** (Wave 9+ audit-gap remediation **DONE** in working tree â€” fail-closed DSSE default, runtime/SDK stubs closed, CI cost/honesty, workspace + Lean Extended, live ops wiring, P3 polish; Dependabot still deferred).

**Reassessment v2 (archived):** [archive/full-repo-audit-reassessment-2026-07-03.md](archive/full-repo-audit-reassessment-2026-07-03.md) — live status is this tracker only.

**North-star:** inventory exit 0 on gated push/schedule workflows (Wave 7 **60/60** @ `7d48b3d4`; Wave 8 **69** gated via honest smokes â€” **not** literal 67/67); **DSSE fail-closed by default** (`PF_ENFORCE_DSSE=0`/`false` opt-out only); live AWS/registry/revocation/edge paths dispatch-only and fail-closed; burn-down + planning docs match code. Wave 9+ (T1â€“T18) **closed** (T12 **ACCEPTED** by policy; Dependabot deferred).

---

## CI baseline (Wave 0 inventory)

Captured via `powershell -File scripts/ci_workflow_inventory.ps1 -Markdown` (2026-07-16; requires `gh` CLI authenticated to repo). Full table: [ci-inventory-latest.md](ci-inventory-latest.md).

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on `main`) | 69 |
| Latest run **success** | 71 |
| Latest run **failure / cancelled** (ungated / PR-only) | 0 |
| No run / unknown | 16 |

**Green snapshot (tip `bae36f642`, 2026-07-18):** inventory exit **0 Ã—2** â€” **69** gated (push/schedule), **0** red after **PR #223** CI-local proofs. Wave 7 historical **60/60** @ `b8b78b94` remains the pre-revive baseline. Do **not** claim literal 67/67.

**No run on main (gated):** none â€” full gated set green.

Re-run: `scripts/ci_workflow_inventory.sh` (Linux/WSL/Git Bash) or `powershell -File scripts/ci_workflow_inventory.ps1` (Windows).

**Note:** **PR #206 merged** at `7d48b3d4`; tip **`b8b78b94`** after **PR #207** (2026-07-16). Inventory **60/60** exit 0 Ã—2. Phase 3 hardening proof + Phase 4 sign-off: [archive/wave7-post-merge-runbook.md](archive/wave7-post-merge-runbook.md) Phase D/E. F23/F24 **DONE**.

---

## Gate command results (Wave 0 + 2026-07-02 local)

| Command | Exit | Notes |
|---------|------|-------|
| `make no-runtime-placeholders` | **0** | `.placeholderignore` + `build/`/`dist/` skip; binary detection (2026-07-02 Phase 0) |
| `python scripts/check_no_placeholder.py` | **0** | Same as above |
| `python scripts/audit_ci_honesty.py` | **0** | 56 justified suppressions; 0 unjustified (Phase 1.6) |
| `cargo build -p retrieval-gateway` | **0** | F05 â€” deps + pf-dsse wired |
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

**Trust-path grep (2026-07-02; default flip Wave 9.1 @ 2026-07-22):** DSSE wired in Go kernel, Rust sidecar/dsse-rs, tool-broker, ledger, TS SDK / dsse-ts. **Unset = enforce** (fail-closed); opt out only with `PF_ENFORCE_DSSE=0`/`false`. When enforcing, trust root required (`PF_TRUST_ROOT_PEM`).

---

## Findings tracker

| ID | Sev | Finding (summary) | Wave | Status | Burn-down | PR | CI proof |
|----|-----|-------------------|------|--------|-----------|-----|----------|
| F01 | P0 | Signature verification stubbed (Go/Rust/TS) | 2 | **DONE** | ST-005, TD-001, TD-003â€“TD-005, TD-008, PH-004 | â€” | `ci.yml` â†’ `reusable-ci-extended.yml` DSSE green on `main`: [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623), [29529736631](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29529736631) |
| F02 | P0 | Shadow mode always allows; `is_tool_enabled` always true | 2 | **DONE** | PH-004, PH-005 | â€” | Compose `PF_ENABLED_TOOLS=` via F21 smoke [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757); in-tree `enabled_tools_deny_by_default` (not in curated `reusable-ci-rust` `--lib`) |
| F03 | P0 | Ledger Docker runs `index-simple.js`; MCP only in `index.ts` | 4 | **DONE** | â€” | â€” | `integration.yaml` MCP tenant tests green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757), [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F04 | P0 | MCP tenant field mismatch (`tid` vs `tenant_id`) | 4 | **DONE** | TD-006 | â€” | Same integration runs as F03 (4 tenant tests) |
| F05 | P0 | `retrieval-gateway` unbuildable | 5 | **DONE** | PH-006 | â€” | `retrieval-gateway.yml` green Ã—2: [29410389588](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588), [28639549745](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549745) |
| F06 | P0 | Ghost integration tests in CI | 1 | **DONE** | â€” | â€” | `tests/integration/test_*.py` (10 pytest smoke tests) |
| F07 | P0 | Broken MCP fraud demo | 5 | **DONE** | â€” | â€” | `demos/verifiable-mcp-fraud/scripts/run-demo.ts` |
| F08 | P0 | Broken edge-middleware example import | 5 | **DONE** | â€” | â€” | Stub removed in structural cleanup; see `docs/guides/demos.md` |
| F09 | P0 | Broken Prisma performance migration | 4 | **DONE** | PH-008 | â€” | Quarantined; `prisma/migrations/README.md`; `migrate deploy` on fresh DB via baseline migration |
| F10 | P0 | Replay Docker CLI invocation bug | 1 | **DONE** | â€” | â€” | `tests/replay/test_docker_invocation.sh` (contract test; merge + Linux CI for cluster green) |
| F11 | P1 | Vacuous Jest gates | 1, 4 | **DONE** | TD-005â€“TD-011 | â€” | Ledger 23+ Jest tests; SDK 4 tests in `reusable-ci-go-node.yml` |
| F12 | P1 | Impacted-test selector format mismatch | 1 | **DONE** | ST-008 | â€” | `tools/test_select_impacted.py` |
| F13 | P1 | Sidecar excluded from PR `cargo test` | 3 | **DONE** | â€” | â€” | `reusable-ci-rust.yml` runs `--test integration_tests` with `PF_SHADOW_MODE=1` |
| F14 | P1 | 4 sidecar integration tests quarantined | 3 | **DONE** | â€” | â€” | `ni_monitor_egress`, `safety_case_bundle`, `events_plan_dsl`, `hardened_adapters` registered in Cargo.toml + CI; 11 tests green |
| F15 | P1 | Sync blocking I/O in async log watcher | 3 | **DONE** | â€” | â€” | `spawn_blocking` in log watcher |
| F16 | P1 | 97 production unwrap/expect/panic in sidecar | 3 | **DONE** | â€” | â€” | `scripts/count_sidecar_unwraps.py --max 10` â€” **0** prod unwrap/expect; shared `time_util`; CI gate in `reusable-ci-rust.yml` |
| F17 | P1 | SDK `verifyTrace` always `{ valid: true }` | 2 | **DONE** | TD-009â€“TD-011 | â€” | `verifyTrace.ts` + Jest |
| F18 | P1 | Demo imports `SentinelOpsClient` | 5 | **DONE** | TD-009 | â€” | SDK exports |
| F19 | P1 | SLO Gates â€” no root lockfile | 1 | **DONE** | â€” | â€” | Mock PF server in workflow |
| F20 | P1 | CodeQL artifact upload broken | 1 | **DONE** | â€” | â€” | `codeql.yaml` matrix |
| F21 | P1 | Runtime components absent from compose | 5 | **DONE** | â€” | â€” | `integration.yaml` compose smoke green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757), [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F22 | P1 | `ws` missing from ledger | 4 | **DONE** | â€” | â€” | `package.json`; `mcp-websocket.test.cjs` smoke stub |
| F23 | P1 | Bench Nightly Criterion regression | 1 | **DONE** | â€” | [#197](https://github.com/SentinelOps-CI/provability-fabric/pull/197), [#198](https://github.com/SentinelOps-CI/provability-fabric/pull/198) | Green Ã—3 on `main` @ `1ab0d2d5`: [29508973817](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973817) (push), [29509027731](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509027731) + [29509041247](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509041247) (`refresh_baseline`); timeout CI overrides + ring-buffer MPMC hang fix |
| F24 | P1 | Paper Conformance sidecar integration failures | 1, 3 | **DONE** | â€” | [#176](https://github.com/SentinelOps-CI/provability-fabric/pull/176) | `paper-conformance.yaml` green Ã—2 on `main` @ `f4b0859e`: [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434) (push), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127) (dispatch); integration gates unchanged |
| F25 | P1 | Egress cert evidence hardcoded accept | 2 | **DONE** | PH-005 | â€” | `env_config::resolve_evidence_hash`; `egress_evidence_enforcement.rs` |
| F26 | P2 | Duplicate ledger entrypoints | 4 | **DONE** | â€” | â€” | `index-simple.ts` / `index-production.ts` removed; single `index.ts` + PROFILE env |
| F27 | P2 | 152 `any` in ledger src | 4 | **DONE** | â€” | â€” | `scripts/count_ledger_any.py --max 20` (0 `any`); `tsconfig.server.json` strict on server/mcp/receipts/egress |
| F28 | P2 | Dual Apollo server stack | 4 | **DONE** | â€” | â€” | `apollo-server-express` removed; `@apollo/server` v4 only; `wave4.test.cjs` |
| F29 | P2 | Duplicate `epsilon_guard.rs` | 5 | **DONE** | â€” | â€” | Single copy in sidecar |
| F30 | P2 | Egress-firewall regex recompiled per call | 3 | **DONE** | â€” | â€” | `lazy_static!` cached regexes |
| F31 | P2 | MD5 for approval token IDs | 3 | **DONE** | â€” | â€” | UUID in tool-broker |
| F32 | P2 | Documentation drift | 5 | **DONE** | â€” | â€” | `make docs-strict` green (2026-07-02 local) |
| F33 | P2 | Lean sorry debt | 6 | **DONE** | LN-* | â€” | [lean-sorry-burn-down.md](lean-sorry-burn-down.md): Invariants **0** + enforced; both Policy trees **0**; MicroInterp **0** â€” `compileClauses`/`semanticsFromClauses`/`dfa_semantics_match` proved; `lake build Runtime`; lean-style ENFORCED not weakened (Extended adapter follow-up) |
| F34 | P2 | Two parallel VS Code extensions | 5 | **DONE** | TD-013 | â€” | [documentation-map.md](../documentation-map.md) Â§ VS Code |
| F35 | P2 | Crate-wide `#![allow(dead_code)]` on sidecar | 3 | **DONE** | â€” | â€” | Module allows removed; lib `-D dead_code` in `reusable-ci-rust.yml` (lib + `integration_tests`); bin scaffold deferred |
| F36 | P3 | No pre-commit hooks | 0 | **DONE** | â€” | Wave 0 | `.pre-commit-config.yaml` |
| F37 | P3 | No root `go.work` | 6 | **DONE** | â€” | â€” | `go.work.example` + `make go-work` + CONTRIBUTING |
| F38 | P3 | ESLint 8.x EOL | 6 | **DONE** | — | — | Root `eslint.config.mjs`; ledger, SDK, console, demos on ESLint 9 |
| F39 | P3 | Dynamic SQL table interpolation | 6 | **DONE** | â€” | â€” | `_validate_table_name` + `ops/retention/test_retention_manager.py` |

---

## Wave summary

| Wave | Focus | Findings | Exit gate | Status (2026-07-02) |
|------|-------|----------|-----------|---------------------|
| 0 | Foundation / truth baseline | F36 | Tracker + burn-down reconciled | **DONE** |
| 1 | CI unblock and honesty | F06, F10â€“F12, F19â€“F24 | Replay green; â‰¥25/67 workflows green | **DONE** â€” F24 closed @ `f4b0859e`; F23 Criterion green Ã—3 on `main` @ `1ab0d2d5` (#197/#198) |
| 2 | Trust chain core | F01â€“F02, F17, F25 | Cross-lang DSSE; fail-closed when enforced | **DONE** |
| 3 | Runtime hardening + sidecar CI | F13â€“F16, F30â€“F31, F35 | Sidecar in PR CI | **DONE** |
| 4 | Ledger + MCP consolidation | F03â€“F04, F09, F11, F22, F26â€“F28 | Docker MCP + Jest suite | **DONE** |
| 5 | Architecture, demos, topology | F05, F07â€“F08, F18, F21, F29, F32, F34 | Demos/examples pass | **DONE** |
| 6 | Quality, docs, formal methods | F33, F37â€“F39 | mkdocs strict; Lean enforced targets | **DONE** â€” F33 closed (MicroInterp **0** sorry + Runtime lake target); F38 done |
| 7 | CI green program | All CI clusters | 60/60 gated green twice on main (honest; not 67/67) | **DONE** â€” tip `b8b78b94`; F23+F24 DONE; inventory exit 0 Ã—2; Phase 3 hardening proof + Phase 4 sign-off recorded |
| 8 | Revive leftovers + Lean | F33 + re-gates | 69 gated exit 0; lean-offline-full; CI-local moto/mock proofs | **DONE** â€” see Wave 8 revive note below |
| 9â€“14 | Audit-gap remediation (T1â€“T18) | Deep-audit 2026-07-22 | See **Wave 9+** section | **DONE** (working tree 2026-07-22); Dependabot deferred |
| E | Engineering speed / scaffolding (non-Lean) | Launch, wiring, CI paths, composite actions | Docs-only &lt;5 min; warm ledger-up &lt;60s; budgets + schedule smoke | **DONE** (working tree 2026-07-22) â€” see **Wave E** |

---

## Phase 0â€“1 prep status (2026-07-02)

| Item | Status | Evidence |
|------|--------|----------|
| Placeholder gate (`make no-runtime-placeholders`) | **DONE** (local) | `.placeholderignore`; `build/`/`dist/`/`site/` skip; binary detection in `check_no_placeholder.py` |
| TRACE-REPLAY-KIT submodule `CMD []` | **DONE** | `external/TRACE-REPLAY-KIT/runner/Dockerfile` ENTRYPOINT + `CMD []` at `957630f` |
| Linux validation checklist | **DONE** | `scripts/linux_validation_checklist.sh` |
| Replay contract in CI | **DONE** (wired) | `integration.yaml` + replay cluster workflows run `test_docker_invocation.sh` |
| CI honesty burn-down | **DONE** (local) | `audit_ci_honesty.py` exit 0; gate in `ci.yml` |
| `passWithNoTests` removed | **DONE** | Ledger / SDK Jest no longer use vacuous pass; marketplace tree removed |
| Sidecar `integration_tests` in PR Rust CI | **DONE** | `reusable-ci-rust.yml` with `PF_SHADOW_MODE=1` |
| Paper-conformance shadow mode | **DONE** (wired) | `paper-conformance.yaml` integration job sets `PF_SHADOW_MODE=1` |
| Criterion `refresh_baseline` | **DONE** | Green Ã—3 @ `1ab0d2d5`; `bench/BASELINE.md` recorded; #197/#198 |

**Wave 7 inventory gate:** **DONE** â€” inventory exit **0** twice on `main` @ `7d48b3d4` (**60/60** gated green); tip `b8b78b94` after #207. Phase 3+4: [archive/wave7-post-merge-runbook.md](archive/wave7-post-merge-runbook.md).

**Wave 8 revive (2026-07-18):** **PR #215** re-gated leftovers with honest smokes; #218â€“#222 lean-offline-full + docs. Tip `3f71ea97`. Inventory **69** gated exit 0. **CI-local proofs follow-up:** `dr-cross` moto path (replaces empty secret-skip), `publish-updates` package/HMAC/mock-registry, `revocation-sync` mock registry merge/sign, `edge-load`/`loadtest`/`perf-proofmeter` hard latency/error asserts + multi-region mock. Do **not** claim literal 67/67.

**Wave 9+ (2026-07-22):** Live DR/publish/revocation/edge-load paths are now **wired** (dispatch-only, fail-closed without secrets); moto/mock remain the gated honesty floor. See [Wave 9+](#wave-9--audit-gap-remediation-2026-07-22) and [live-ops-secrets.md](../runbooks/live-ops-secrets.md).

---

## Audit remediation program verification (2026-07-02)

| Metric | Result |
|--------|--------|
| `count_sidecar_unwraps.py --max 10` | **0** (exit 0) |
| `count_ledger_any.py --max 20` | **0** (exit 0) |
| `audit_ci_honesty.py` | exit **0** (56 justified, 0 unjustified) |
| `check_no_placeholder.py` | exit **0** |
| `cargo test -p sidecar-watcher --test integration_tests` | **9/9** pass |
| `cargo test -p sidecar-watcher --test ni_monitor_egress â€¦ hardened_adapters` | wired in CI |
| `python tests/crypto/test_cross_lang_dsse.py` | pass |
| `cd runtime/ledger && npm test` | **23 passed**, 1 skipped |
| `RUSTFLAGS=-D dead_code cargo test -p sidecar-watcher --lib` | pass |


`tests/replay/test_docker_invocation.sh` documents the F10 Docker contract (ENTRYPOINT `python replay_run.py`, not `bash replay_run.sh`). Skips gracefully without Docker/submodule. **Replay cluster workflows** (`platform-replay.yml`, `nightly-replay.yml`, `platform-cert-validate.yml`) require merge to `main` + Linux validation before marking green.

---

## Wave 9+ â€” Audit-gap remediation (2026-07-22)

Source: deep audit canvas @ tip `d1db030ea` (findings **T1â€“T18**). Builds on Waves 0â€“8 (**DONE**). All waves **implemented in working tree** (2026-07-22). Dependabot conflict program remains **deferred** (not a T-finding blocker).

### Wave status

| Wave | Focus | Findings | Status |
|------|-------|----------|--------|
| 9.1 | DSSE fail-closed by default | T1 | **DONE** |
| 9.2 | README + deployment trust honesty | T2 | **DONE** |
| 9.3 | Stale planning docs refresh | T8, T9 | **DONE** |
| 10.1 | Tool-broker tenant/risk/throttle/budget | T3 | **DONE** |
| 10.2 | Ledger MCP sliding-window rate limit + counters | T4 | **DONE** |
| 10.3 | TS SDK HTTP client + idempotent retry | T5 | **DONE** (TD-009/010/011 **DONE**) |
| 10.4 | SWE-bench mock vs OpenHands stress split | T6 | **DONE** |
| 11.1â€“11.3 | Multiarch / Criterion / paper-conformance cost | T10, T11 (+ paper cost) | **DONE** |
| 11.4â€“11.5 | Soft-fail harden + Windows smoke + WSL-first | T14, T16 | **DONE** (honesty **50** justified) |
| 12.1 | Orphaned crates in Cargo workspace | T7 | **DONE** |
| 12.2 | ActionDSL.Extended + MicroInterp adapter + ENFORCED | T13; T12 **ACCEPTED** | **DONE** |
| 13 | Live DR / publish / revocation / edge-load | T15 | **DONE** (dispatch-only, fail-closed) |
| 14 | LabelerGen/ExportDFA + policy-kernel Redis | T17, T18 | **DONE**; Dependabot **deferred** |

### Findings T1â€“T18

| ID | Sev | Finding (summary) | Wave | Status | Proof / notes |
|----|-----|-------------------|------|--------|---------------|
| T1 | P0 | DSSE fail-open by default | 9.1 | **DONE** | Go/Rust/TS/dsse-ts/ledger/sidecar: unset â†’ enforce; opt-out `PF_ENFORCE_DSSE=0`/`false`; trust root required when enforcing |
| T2 | P0 | README overclaims formal guarantees | 9.2 | **DONE** | README conditional claims; [deployment-guide.md](../guides/deployment-guide.md) trust section fail-closed default |
| T3 | P1 | Tool-broker TODOs still live | 10.1 | **DONE** | Tenant fail-closed default (`PF_ENFORCE_TENANT=0` opt-out); no unverified JWT spoof; risk from allow-list; throttle sleep; real `budget_consumed_*` |
| T4 | P1 | Ledger MCP rate-limit/counters incomplete | 10.2 | **DONE** | `sliding-window-rate-limiter.ts`; proxy counters; JCS hit-rate (single-node caveat documented) |
| T5 | P1 | TS SDK gRPC + retry still stubbed | 10.3 | **DONE** | HTTP client lifecycle; idempotent outbound retry; TD-009/010/011 **DONE** (gRPC deferred by design) |
| T6 | P1 | SWE-bench stress green on mock | 10.4 | **DONE** | Mock pipeline smoke vs OpenHands stress split; OpenHands eval fail-closed (no `\|\| true`); [ci-reference.md](../reference/ci-reference.md) |
| T7 | P1 | Out-of-workspace Rust crates | 12.1 | **DONE** | `telemetry-service`, `jwks-manager`, `mpc-fintech`, `egress-firewall` in workspace; egress CI `--no-default-features` |
| T8 | P1 | Placeholder burn-down + inventory stale | 9.3 | **DONE** | [burn-down.md](placeholders/burn-down.md), [inventory.md](placeholders/inventory.md) refreshed; TD-001/002/006/007/010/011 **DONE** |
| T9 | P1 | ci-health-matrix / evidence-v0.2-status outdated | 9.3 | **DONE** | Matrix archives 13/68; evidence-v0.2 stamped historical; live counts in evidence-program-closure |
| T10 | P2 | Multi-arch Docker ~47 min wall | 11.1 | **DONE** | Path filters; push/PR amd64-only; schedule/tags dual-arch (`ubuntu-24.04-arm`) |
| T11 | P2 | Criterion nightly ~25 min | 11.2 | **DONE** | Smoke on PR/push; compare/baseline schedule + dispatch only |
| T12 | P2 | Lean full offline schedule/dispatch only | 12.2 / policy | **ACCEPTED** | Intentional: MicroInterp smoke on PR; full mathlib Monday/dispatch only (not every-PR) |
| T13 | P2 | MicroInterp Extended.Event adapter unfinished | 12.2 | **DONE** | `ActionDSL.Extended` + `Runtime/ExtendedAdapter.lean` lake roots; ENFORCED sorry scan; **mathlib-backed** â€” built on `lean-offline-full` (`lake build ActionDSL.Extended Runtime.ExtendedAdapter`), not PR smoke |
| T14 | P2 | Soft-fail / honesty cluster (~62 â†’ ~51) | 11.4 | **DONE** | Soft-fail harden set; `audit_ci_honesty.py` exit 0 â€” **50** justified, 0 unjustified (OpenHands eval soft-ignore removed) |
| T15 | P2 | Live AWS DR / publish / revocation deferred | 13 | **DONE** | Dispatch-only live paths fail-closed; DR uses `--verify-only`; `--confirm` implements schema+DNS mutation; moto/mock remain gated floor |
| T16 | P2 | Windows second-class for Lean/OpenHands | 11.5 | **DONE** | WSL-first documented; `test-windows.yml` subset smoke (no native Lean chase) |
| T17 | P3 | LabelerGen / ExportDFA placeholder TODOs | 14 | **DONE** | Deterministic Lean `hash` (not cryptographic); ExportDFA docs honest about integrity hashing |
| T18 | P3 | Redis cache TODOs in policy-kernel | 14 | **DONE** | Redis L2 in `DecisionCache` + `OptimizedDecisionCache` when `redisAddr` set; miniredis tests |

**Also in Wave 11.3 (no dedicated T-ID):** paper-conformance path-tighten / shard; full suite remains nightly.

### Wave 13 â€” Live ops (locked include)

| Path | Workflow | Gated floor | Live path | Status |
|------|----------|-------------|-----------|--------|
| Cross-region DR | `dr-cross.yaml` | moto | `workflow_dispatch` `mode=live` | **DONE** â€” fail-closed preflight (`scripts/dr/live_dr_preflight.py`) |
| Registry publish | `publish-updates.yaml` | dry-run + mock | `dry_run=false` | **DONE** â€” `live_registry: true` artifact when secrets present |
| Revocation sync | `revocation-sync.yaml` | dry-run mock | `mode=live` | **DONE** â€” `scripts/revocation/live_registry_sync.py` |
| Edge load | `edge-load.yaml` | smoke mock | `mode=full` | **DONE** â€” fail-closed without `EDGE_REGION_URLS` |

Runbook: [live-ops-secrets.md](../runbooks/live-ops-secrets.md). Ops still must configure secrets and dispatch to prove against real backends; inventory exit 0 must **not** depend on live secrets.

### Deferred (non-blocking)

| Item | Status | Notes |
|------|--------|-------|
| Dependabot conflict program | **Deferred** | Separate follow-up; see runbook note |
| Redis-backed multi-instance MCP rate limits | Out of scope | Single-node sliding window documented |
| Full gRPC TS SDK | Out of scope | HTTP covers current consumers |
| Native Windows Lean/OpenHands | Out of scope | WSL-first |
| Full mathlib `lake build` on every PR | Out of scope | Monday/dispatch `lean-offline-full` only |

### Local verification snapshot (2026-07-22)

| Check | Result |
|-------|--------|
| `python scripts/audit_ci_honesty.py` | exit **0** â€” **50** justified, 0 unjustified |
| DSSE default (ports) | unset â†’ enforce across Go/Rust/TS/ledger/sidecar |
| Workspace members | orphaned crates listed in root `Cargo.toml` |
| Lean ENFORCED | MicroInterp + Extended + ExtendedAdapter; Extended lake-build on `lean-offline-full` |
| Live workflows | dispatch-only; fail-closed comments + preflight scripts present |

### Wave 9+ completion / verification (2026-07-22, adversarial pass)

Parallel agents had marked Wave 9+ **DONE** while burn-down/inventory still listed TD-001/002/006/007 OPEN and tenant enforce was opt-in. This pass **fixed** rather than papered over:

| Item | Verified / fixed |
|------|------------------|
| Tracker â†” burn-down â†” inventory | TD-001/002/006/007/010/011 **DONE**; inventory Redis/LabelerGen claims refreshed |
| DSSE opt-in docs | `merge-pr-body.md`, reassessment 2026-07-02 corrected to fail-closed default |
| Tool-broker tenant | `PF_ENFORCE_TENANT` unset=enforce; deny missing tenant; **reject unverified JWT** tenant spoof |
| `blue_green_migrate.sh --confirm` | Implements prisma/`PF_BG_MIGRATE_CMD` + Route53 UPSERT (was exit 1); live DR CI stays `--verify-only` |
| Historical 8/67 | Stamped in `evidence-acceptance-positioning.md` + CHANGELOG |
| Lean T13 honesty | ENFORCED Extended + ExtendedAdapter; `lake build ActionDSL.Extended Runtime.ExtendedAdapter` on lean-offline-full |
| SWE OpenHands eval | Removed `\|\| true` soft-fail when secrets present |
| `auth-simple.ts` | Prod/profile guard refuses production |
| `OptimizedDecisionCache` | Redis L2 via `DecisionCache` when `redisAddr` set |

**Focused tests (this pass):** `cargo test -p tool-broker` (tenant suite); `cargo test -p pf-dsse --lib`; Go `core/crypto/dsse`; Redis `TestRedis*`; ledger `mcp-rate-limit`; SDK jest; `audit_ci_honesty.py`.

**Residual OPEN / deferred (honest):**

| Item | Status |
|------|--------|
| Dependabot conflict program | Deferred (non-blocking) |
| Redis-backed multi-instance MCP rate limits | Out of scope (single-node documented) |
| Full gRPC TS SDK | Out of scope (HTTP covers consumers) |
| Native Windows Lean/OpenHands | Out of scope (WSL-first) |
| Full mathlib `lake build` on every PR | Out of scope (T12 ACCEPTED) |

**Closed this pass (2026-07-22):** `policykernel/compiler` DFA unit tests â€” last-condition transitioned via synthetic `condition_satisfied` hop so `Evaluate`/`EvaluatePath` never reached accepting states; compiler now accepts on the final real condition event; `go test ./compiler/` green.

---

## Wave E (Engineering) â€” speed and scaffolding (2026-07-22)

Non-Lean program: unify launch/wiring, slash CI install tax, share setup scaffolding. **Out of scope:** Lean/mathlib, Dependabot conflict program, full gRPC SDK. Budgets: [engineering-latency-budget.md](engineering-latency-budget.md). Schedule guard: `.github/workflows/engineering-budget-smoke.yml`.

### North-star before â†’ after (estimates)

| Metric | Before (pre-E) | After (E1â€“E5 landed) | Status |
|--------|----------------|----------------------|--------|
| Docs-only `main` push gated wall-clock | Full `ci.yml` language matrix (Rust 120m budget + Go/Node multi-`npm ci` + extended) | Path-conditioned: docs/figs skip Rust/Go-Node/extended/Lean slices; target **&lt;5 min** gated | **Landed** (E3.1) â€” measure per budget doc |
| Sidecar-only PR | Broad Go/Node + console install tax; full-ish Rust workspace pressure | Impacted Rust crates + nextest; Go/Node parallel slices; console path-scoped | **Landed** (E3.2â€“E3.3) |
| Warm `make ledger-up` â†’ GraphQL healthy | `demo-up --build` + fixed `sleep 30` / heavy default compose | `ledger-up` + `--wait`, no `--build` on warm path; target **&lt;60s** | **Landed** (E1) â€” local measure |
| Compose / wiring feedback | Misaligned ports; discover-after-boot | `check_wiring.py` + `compose-smoke`; pf-env schema | **Landed** (E1â€“E2) |
| Always-on CI burners | CodeQL/ops/scorecard/schema on many pushes | Schedule and/or path-filter (Wave 11 multiarch/Criterion/paper **not** re-expanded) | **Landed** (E3.4; preserves Wave 11) |
| Contributor setup | K8s implied; duplicated Actions setup; 25 go.mod islands | `local-workflows.md`; composite actions; `go-work-init`; path-aware `install-dev`; Kind path-gated | **Landed** (E4) â€” reusable Go/Node composites adopted |

### Wave status

| Wave | Focus | Status |
|------|-------|--------|
| E1 | Unified Make/just launch, local-workflows, compose PROFILE=dev, health-wait | **DONE** (working tree) |
| E2 | Port/URL wiring, MCP keep-alive, pf-env schema, SDK cleanup | **DONE** (working tree) |
| E3.1 | Path-condition `ci.yml` push jobs | **DONE** (working tree) |
| E3.2â€“E3.3 | Split reusable Rust / Go-Node; npm workspaces; impacted installs | **DONE** (working tree) |
| E3.4â€“E3.5 | Schedule/path-filter burners; inventory + ci-reference honesty | **DONE** (working tree) |
| E4 | Composite actions, go-work-init, install-dev, Kind/pytest scoping | **DONE** (working tree) |
| E5 | Latency budget doc + tracker + optional schedule smoke | **DONE** (this section) |

### Spot-check â€” E1â€“E4 artifacts present

| Artifact | Present |
|----------|---------|
| `Makefile` `platform-up` / `ledger-up` / `compose-smoke` / `check-wiring` | Yes |
| `docs/dev/local-workflows.md` | Yes |
| `ci.yml` `dorny/paths-filter` (push-symmetric slices) | Yes |
| `reusable-ci-rust.yml` impacted + nextest parallel jobs | Yes |
| `reusable-ci-go-node.yml` parallel go-cli / ledger-node / â€¦ | Yes |
| Root `package.json` workspaces | Yes |
| `.github/actions/setup-{node-workspace,go-cli,python-tests}` | Yes |
| `scripts/check_wiring.py`, `schemas/pf-env.schema.json` | Yes |
| `scripts/go-work-init.sh`, `scripts/install-dev.sh` | Yes |
| `integration.yaml` Kind path-gate | Yes |

### Residual / follow-ups (honest)

| Item | Notes |
|------|-------|
| `reusable-ci-go-node.yml` adopt `setup-go-cli` / `setup-node-workspace` | **CLOSED** (2026-07-22) â€” go-cli, ledger-node, sdk-node, console use composites; pcs-spectral keeps plain `setup-node` (global spectral only) |
| First green `engineering-budget-smoke` on `main` | Schedule/dispatch-only; inventory will treat it as gated once present â€” dispatch after merge for a green last-run |
| Docs-only / sidecar-only minute claims | Estimates above; record real Actions medians in a follow-up note when measured on `main` |
| Cold GHA compose vs local warm budgets | Do not equate; see cache-warm note in budget doc |
| Wave 11 wins | Do **not** re-expand multiarch dual-arch on every PR, Criterion full compare on push, or paper-conformance full suite on every tip |

---

## References

- Original audit: [archive/full-repo-audit-2026-07-01.md](archive/full-repo-audit-2026-07-01.md)
- Reassessment v1: [archive/full-repo-audit-reassessment-2026-07-02.md](archive/full-repo-audit-reassessment-2026-07-02.md)
- **Reassessment v2 (POST-remediation):** [archive/full-repo-audit-reassessment-2026-07-03.md](archive/full-repo-audit-reassessment-2026-07-03.md)
- [Placeholder burn-down](placeholders/burn-down.md)
- [CI health matrix](ci-health-matrix.md)
- Historical archive policy: [archive/README.md](archive/README.md)
- [Evidence program closure](../roadmap/evidence-program-closure.md)
- [Ledger consolidation RFC](ledger-consolidation-rfc.md)
- [Lean sorry burn-down](lean-sorry-burn-down.md)
- [Live ops secrets](../runbooks/live-ops-secrets.md) (Wave 7 archive: [wave7-post-merge-runbook.md](archive/wave7-post-merge-runbook.md))
- [Engineering latency budgets (Wave E5)](engineering-latency-budget.md)
