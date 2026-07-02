# Full Repository Audit — 2026-07-01

Evidence-based audit of `provability-fabric`. Findings are labeled **verified** (command run or file read on this date) or **suspected** (static analysis only, not runtime-confirmed).

---

## Executive Summary

Provability Fabric is a **real, substantial polyglot monorepo** (~85 GitHub workflows, Lean + Rust + Go + Node + Python) with **working Evidence v0.1/v0.2 and PCS lanes**, but **incomplete platform integration** and **repo-wide CI that is not green**.

| Area | Posture |
|------|---------|
| Evidence lane (schemas, Go pack/validate/replay, pytest) | **Solid** — verified green in CI matrix docs |
| PCS adapter | **Solid** — documented + benchmarked |
| Platform enforcement / trust chain | **Weak** — structural validation exists; Ed25519/DSSE verification largely stubbed |
| CI honesty | **Poor** — vacuous test gates, ghost tests, `continue-on-error`, widespread `\|\| true` |
| Ledger / MCP | **Fragmented** — 3 entrypoints (317/324/717 lines), Docker runs `index-simple.js`, zero Jest tests |
| Developer UX (Windows) | **Second-class** — many tests skip; SWE-bench real engine needs Linux/WSL |
| Repo-wide CI on `main` | **Not green** — **13/67** gated workflows green (verified 2026-07-02); replay cluster shares one CLI bug |

**Honest bottom line:** The repo is not a hollow scaffold. The Evidence and PCS paths are production-quality for their scope. The platform/runtime layer has significant integration debt, cryptographic stubs, and CI false-confidence patterns that must be addressed before claiming end-to-end formal guarantees.

### Phase 2 verification snapshot (2026-07-02, Windows)

| Command | Result |
|---------|--------|
| `git submodule status` | **Pass** — `external/CERT-V1` @ `61ad3e5`, `external/TRACE-REPLAY-KIT` @ `957630f` |
| `ls external/` | `CERT-V1`, `TRACE-REPLAY-KIT`, `.gitkeep`, `README.md` |
| `cd core/cli/pf && go test ./...` | **Pass** — `pf/cmd` ok; root `pf` has no test files |
| `cargo test --workspace --exclude provability-fabric-core-sdk-rust --exclude sidecar-watcher --exclude labeler --exclude tool-broker` | **Pass** — attestor, kms-proxy, wasm-sandbox (2 tests), adapters (5 tests) |
| `demos/verifiable-mcp-fraud/scripts/run-demo.ts` | **Missing** — only `setup-demo.ts` exists |
| CI inventory (PowerShell equivalent of `scripts/ci_workflow_inventory.sh`) | **13 green / 51 red-or-in-progress / 3 no_run** of 67 gated workflows |
| `gh run list --branch main --limit 50` | Mixed — evidence/smoke green; replay/CERT/SLO/CodeQL failing |

---

## P0–P3 Findings Table

| ID | Sev | Finding | Path | Status | Repro | Effort |
|----|-----|---------|------|--------|-------|--------|
| F01 | P0 | Signature verification stubbed across Go/Rust/TS — receipts pass on structure only | `core/policy-kernel/engine.go:566`, `runtime/sidecar-watcher/src/{plan,broker}.rs`, `runtime/tool-broker/src/main.rs:380`, `runtime/ledger/src/{receipts,egress}.ts` | verified | Read `verifyReceipt` / `verify_receipt` / `verifyReceiptSignature` bodies | L |
| F02 | P0 | Shadow mode always allows; `is_tool_enabled` always true | `runtime/sidecar-watcher/src/policy_adapter.rs:365-372`, `permit_enforcement.rs:388-390` | verified | Read enforcement paths | M |
| F03 | P0 | Ledger Docker runs `index-simple.js`; MCP only wired in `index.ts` | `runtime/ledger/Dockerfile:36`, `src/index.ts` vs `index-simple.ts` | verified | Dockerfile CMD vs MCP mount | M |
| F04 | P0 | MCP tenant context lost: auth sets `tid`, proxy reads `tenant_id` | `runtime/ledger/src/auth.ts`, `mcp/mcp-proxy.ts` | verified | Grep field names | S |
| F05 | P0 | `retrieval-gateway` unbuildable — no Cargo.toml or go.mod | `runtime/retrieval-gateway/` | verified | Rust+Go sources, no manifest | M |
| F06 | P0 | Ghost integration tests in CI reference missing files | `.github/workflows/operational-excellence.yaml:287-296` | verified | Files absent from `tests/integration/` | S |
| F07 | P0 | Broken MCP fraud demo — `run-demo.ts` missing | `demos/verifiable-mcp-fraud/package.json:16`, `scripts/` | verified | Only `setup-demo.ts` in `scripts/` | S |
| F08 | P0 | Broken edge-middleware example — package `@provability-fabric/sdk` does not exist | `examples/edge-middleware/index.ts:1` | verified | Actual package: `@provability-fabric/core-sdk-typescript` | S |
| F09 | P0 | Broken Prisma performance migration references non-existent columns | `runtime/ledger/prisma/migrations/20250101000000_optimize_performance/` | verified | Read migration SQL vs `schema.prisma` | M |
| F10 | P0 | Replay CI failures — `replay_run.py: error: unrecognized arguments: bash replay_run.sh` | Platform Replay, Nightly Replay, Platform CERT | verified | `gh run view --log-failed` on 28500339563, 28568693881, 28568431511 | M |
| F11 | P1 | CI vacuous gates — Jest passes with zero tests | `runtime/ledger/package.json:15`, `core/sdk/typescript/package.json` | verified | `"test": "jest --passWithNoTests"`; 0 `*.test.ts` in ledger | S |
| F12 | P1 | Impacted-test selector format mismatch | `tools/select_impacted.py` vs `reusable-ci-extended.yml` | verified | Emits `python_test:name`; workflow expects file paths | S |
| F13 | P1 | Large Rust crates excluded from PR `cargo test` | `.github/workflows/reusable-ci-rust.yml` | verified | Excludes sidecar-watcher, labeler, tool-broker, core-sdk-rust | M |
| F14 | P1 | 4 sidecar integration tests quarantined (API drift) | `runtime/sidecar-watcher/Cargo.toml:64-65`, `tests/{ni_monitor_egress,safety_case_bundle,events_plan_dsl,hardened_adapters}.rs` | verified | Not in `[[test]]` table; comment in Cargo.toml | M |
| F15 | P1 | Sync blocking I/O inside async log watcher; zero `spawn_blocking` under `runtime/` | `runtime/sidecar-watcher/src/main.rs:635-657` | verified | `File::open` + line iteration in async loop | M |
| F16 | P1 | 97 production `unwrap`/`expect`/`panic!` in sidecar src (18 in scheduler alone) | `runtime/sidecar-watcher/src/scheduler.rs` (+ 32 files) | verified | Python count script 2026-07-02 | M |
| F17 | P1 | SDK `verifyTrace` always returns `{ valid: true }` | `core/sdk/typescript/src/index.ts:28-31` | verified | Read code | S |
| F18 | P1 | Demo imports `SentinelOpsClient`; SDK exports `ProvabilityFabricSDK` | `demos/verifiable-mcp-fraud/src/*.ts`, `core/sdk/typescript/src/index.ts` | verified | Grep exports vs imports | S |
| F19 | P1 | SLO Gates fail — no root lockfile for Node setup | SLO Gates run 28568369544 | verified | `Dependencies lock file is not found` | S |
| F20 | P1 | CodeQL fails — artifact `codeql-database` not found | CodeQL run 28429083030 | verified | `gh run view --log-failed` | M |
| F21 | P1 | 15/16 runtime components absent from root docker-compose | `docker-compose.yml` vs `runtime/*` | verified | Only sidecar-adjacent services in default compose | M |
| F22 | P1 | `ws` package missing from ledger dependencies (WebSocket MCP) | `runtime/ledger/package.json`, `mcp/mcp-service.ts` | verified | package.json vs import | S |
| F23 | P1 | Bench Nightly Criterion fails on regression compare | Bench run 28498540107 | verified | `Criterion regression detected` | M |
| F24 | P1 | Paper Conformance CI fails in sidecar integration tests | Paper run 28497725814 | verified | `integration_tests.rs` exit code 1 | M |
| F25 | P1 | Egress cert evidence hardcoded to accept in sidecar main | `runtime/sidecar-watcher/src/main.rs:505-530` | verified | `permit_decision: "accept"`, `path_witness_ok: true` | M |
| F26 | P2 | Duplicate ledger entrypoints (~60-70% duplicated) | `runtime/ledger/src/index{,-simple,-production}.ts` | verified | 317 / 324 / 717 lines | L |
| F27 | P2 | 152 `any` usages in ledger src | `runtime/ledger/src/**/*.ts` | verified | Grep count | M |
| F28 | P2 | Deprecated `apollo-server-express` alongside `@apollo/server` | `runtime/ledger/package.json:21-24` | verified | Dual Apollo stack | S |
| F29 | P2 | Duplicate `epsilon_guard.rs` (orphan at `runtime/privacy/`) | `runtime/privacy/epsilon_guard.rs` (274 lines) vs `sidecar-watcher/src/privacy/` (379 lines) | verified | `fc` shows diverged copies | S |
| F30 | P2 | Egress-firewall regex recompiled per detection call | `runtime/egress-firewall/src/main.rs:248+` | verified | `Regex::new(...).unwrap()` inside methods | S |
| F31 | P2 | MD5 used for approval token IDs | `runtime/sidecar-watcher/src/revocation.rs:214` | verified | `md5::compute` | S |
| F32 | P2 | Documentation drift — evidence overview stale, on-ramps broken links | `docs/evidence/overview.md`, `on-ramps/README.md` | verified | Read docs | M |
| F33 | P2 | Lean `sorry` debt (24 occurrences in core proofs) | `core/lean-libs/Invariants.lean` (14), `proofs/Policy.lean` (4), etc. | verified | Grep count | L |
| F34 | P2 | Two parallel VS Code extensions | `vscode-extension/` vs `tools/vscode-ext/` | verified | Different package names/purposes | S |
| F35 | P2 | Crate-wide `#![allow(dead_code)]` on sidecar lib | `runtime/sidecar-watcher/src/lib.rs:4` + 3 module-level allows in `main.rs` | verified | Read lib.rs | S |
| F36 | P3 | No pre-commit hooks | No `.pre-commit-config.yaml` | verified | Glob search | M |
| F37 | P3 | No root `go.work` — manual replace wiring | Multiple `go.mod` files | verified | Structure | M |
| F38 | P3 | ESLint 8.x EOL across frontend packages | `console/package.json`, etc. | verified | Read manifests | M |
| F39 | P3 | Dynamic SQL table interpolation | `ops/retention/retention_manager.py:132` | verified | Read code | S |

---

## User-Path Matrix

| Path | Windows native (verified 2026-07-02) | WSL/Linux | Notes |
|------|--------------------------------------|-----------|-------|
| Minimal CLI (`core/cli/pf`) | **Pass** — `go test ./...` ok | Pass | `pf` root has no test files |
| Rust workspace (excluded crates) | **Pass** — attestor, kms-proxy, wasm-sandbox, adapters | Pass | sidecar/labeler/tool-broker excluded from PR CI run |
| Evidence validate/pack (`pf evidence`) | **Pass** (CI-backed) | Pass | Not re-run locally this session |
| Evidence replay execute | **Skip** | Pass with submodules | Windows pytest skips |
| Runtime evidence live sidecar | **Skip** | Pass with CERT-V1 submodule | Submodules initialized locally |
| SWE-bench real engine | **Skip** | Pass with OpenHands | Mock engine only on Windows |
| `examples/evidence-basic` | **Pass** (CI-backed) | Pass | pytest in CI |
| `examples/forensic-replay-basic` | **Pass** (CI-backed) | Pass | pytest in CI |
| `examples/runtime-evidence-basic` | **Partial** — static path works; `--live` needs bash/submodules | Pass | |
| `demos/verifiable-mcp-fraud` | **Fail** — missing `run-demo.ts`, wrong SDK export | Fail | `npm run demo:run` → missing script |
| `examples/edge-middleware` | **Fail** — nonexistent npm package | Fail | `@provability-fabric/sdk` import |
| Full platform (`docker compose up`) | **Suspected partial** | Suspected partial | ledger/tool-broker/egress-firewall not in root compose |
| `make test` (full) | **Not run** | Suspected partial | Lean/replay paths Linux-heavy |
| External standards | **Pass locally** | Pass with token | Requires `make submodules` on fresh clone |

**Submodules (verified):** `external/CERT-V1` and `external/TRACE-REPLAY-KIT` at heads/main.

---

## CI Workflow Matrix

### Gated workflow inventory (verified 2026-07-02)

PowerShell equivalent of `scripts/ci_workflow_inventory.sh` (bash unavailable on Windows path):

| Metric | Count |
|--------|-------|
| Gated workflows (push/schedule on `main`) | **67** |
| Latest run **success** | **13** |
| Latest run **failure / in_progress** | **51** |
| No run on `main` | **3** (`policy-build.yml`, `release.yaml`, `verify-publish-bundle.yaml`) |

**Green workflows (13):** `actionlint.yml`, `bench-swebench-smoke.yaml`, `cert-validate.yml`, `chaos-nightly.yaml`, `ci.yml`, `ci-nightly-pytest.yml`, `ci-weekly-full.yml`, `evidence.yaml`, `evidence-v01-smoke.yml`, `proof-bot.yaml`, `proto-compat.yaml`, `scorecards.yml`, `standards-pin.yml`.

**Representative failures (51):** replay cluster (`platform-replay.yml`, `nightly-replay.yml`, `platform-cert-validate.yml`, `replay.yml`, `morph-replay.yml`), security (`codeql.yaml`, `cargo-deny.yml`, `wasm-scan.yaml`), Lean (`lean-offline.yaml`, `lean-style.yaml`, `lean-morph.yaml`), platform ops (`slo-gates.yaml`, `operational-excellence.yaml`, `billing-test.yaml`), bench/perf (`bench-nightly-criterion.yaml`, `paper-conformance.yaml`, `performance-gate.yaml`).

Closure doc still cites **12/67** (`docs/roadmap/evidence-program-closure.md`); live inventory now shows **13/67** — marginal improvement, still exit code 1.

### Top failing scheduled workflows — root cause triage (verified via `gh run view --log-failed`)

| Workflow | Run ID | Conclusion | Root cause |
|----------|--------|------------|------------|
| Platform Replay Tests | 28500339563 | failure | `replay_run.py: error: unrecognized arguments: bash replay_run.sh` |
| Nightly Replay | 28568693881 | failure | Same replay CLI invocation bug |
| Platform CERT Validation | 28568431511 | failure | Same — Docker replay runner passes shell wrapper as Python arg |
| Bench Nightly Criterion | 28498540107 | failure | `Criterion regression detected (see bench/README.md thresholds)` |
| Paper Conformance CI | 28497725814 | failure | Sidecar `integration_tests.rs` failed (Rate Limits Performance job) |
| SLO Gates | 28568369544 | failure | `Dependencies lock file is not found` — no root `package-lock.json` |
| CodeQL Security Analysis | 28429083030 | failure | `Unable to download artifact(s): Artifact not found for name: codeql-database` |

**False-green patterns (verified static):**
- `jest --passWithNoTests` in ledger + TS SDK
- `operational-excellence.yaml` ghost pytest files (lines 287-296)
- `ci-nightly-pytest.yml` `continue-on-error: true` on integration
- `bench-swebench-smoke.yaml` Rust `continue-on-error: true`
- 47 workflow files contain `|| true`

---

## Component Scorecards

### Sidecar-watcher (Phase 3 deep dive)

| Dimension | Score | Detail |
|-----------|-------|--------|
| Structural enforcement | B | Event routing, role-based policy adapter, epoch/revocation checks |
| Crypto trust | F | `verify_receipt` structural only; CERT sig defaults to `"unconfigured"`; egress cert evidence hardcoded accept |
| Reliability | C- | 97 production unwrap/expect/panic; 18 in `scheduler.rs`; sync I/O in async watcher |
| Test coverage | D | 4 integration tests quarantined; excluded from PR `cargo test` |
| dead_code | D | Crate-wide `#![allow(dead_code, unused_variables)]` on lib.rs; 3 `#[allow(dead_code)]` in main.rs |

**Production unwrap/expect/panic counts (top offenders, verified 2026-07-02):**

| File | Production | In test modules |
|------|------------|-----------------|
| `scheduler.rs` | 18 | 22 |
| `revocation.rs` | 14 | 1 |
| `ni_monitor.rs` | 9 | 0 |
| `witness.rs` | 8 | 2 |
| `break_glass.rs` | 7 | 13 |
| `main.rs` | 6 | 0 |
| **Total src/** | **97** | **183** |

**Quarantined integration tests (4):**

| Test file | Why quarantined |
|-----------|-----------------|
| `tests/ni_monitor_egress.rs` | Imports `EgressCertManager`, `NIMonitor`, `NIVerdict` types — API surface changed; not registered in `Cargo.toml [[test]]` |
| `tests/safety_case_bundle.rs` | Uses `SafetyCaseBuilder`, `SafetyCaseStore` — bundle retention/compression API drift |
| `tests/events_plan_dsl.rs` | Uses `EventMediator`, `PlanNode`, `TypedEvent` — plan DSL mediation API changed |
| `tests/hardened_adapters.rs` | Spawns adapter binaries via `Command` — effect allowlist/hardening API drift |

CI gates use `--lib` tests only (`emit_evidence_tests`, `dfa_equiv`, `integration_tests` when not broken).

**Async IO issue (`main.rs:635-657`):** `watch_container_logs` runs inside `tokio` but uses synchronous `File::open`, `BufReader`, and blocking line iteration. No `spawn_blocking` anywhere under `runtime/`. Blocks the async executor on every log read pass.

**Scheduler mutex risk:** 18 production `.unwrap()` on `Mutex::lock()` in `scheduler.rs`. Poisoned mutex → process panic. Combined with `panic = "abort"` in release profile.

### Trust chain (Phase 3 deep dive)

Trace: plan submission → policy-kernel → sidecar enforcement → tool-broker → ledger receipts → SDK client.

| Layer | File | Implemented | Stubbed / permissive |
|-------|------|-------------|---------------------|
| Policy kernel | `core/policy-kernel/engine.go` | Plan structural validation, label flow, tenant/capability checks, PF signature *signing* (`pf_sig.go`) | `validateReceipt` line 566: "structural validation only until wired" — no Ed25519 verify |
| Sidecar plan | `runtime/sidecar-watcher/src/plan.rs:407-429` | Receipt field validation | Ed25519 verify commented out; returns `Ok(())` |
| Sidecar broker | `runtime/sidecar-watcher/src/broker.rs:259-274` | Same structural checks | Logs "Receipt verified" without crypto |
| Sidecar permit | `runtime/sidecar-watcher/src/permit_enforcement.rs` | Event routing, tool rejection path, CERT-V1 emission | `is_tool_enabled` → always `true`; CERT sig from env or `"unconfigured"` |
| Sidecar policy | `runtime/sidecar-watcher/src/policy_adapter.rs` | Role-based permit rules; witness deny-by-default in high-assurance | Shadow mode always allows (372); `WorldState.has_path_witness` simulates via HashMap presence |
| Tool broker | `runtime/tool-broker/src/main.rs:368-381` | Receipt structure + empty sig check | "Structural validation only until Ed25519 verify is wired" |
| Ledger receipts | `runtime/ledger/src/receipts.ts:245-265` | Hash + alg check | `return receipt.sign_alg === 'ed25519' && receipt.sig.length > 0` |
| Ledger egress | `runtime/ledger/src/egress.ts:314-333` | Hash prefix length check | No Ed25519; returns true on 64-char hashes |
| Ledger MCP | `runtime/ledger/src/mcp/mcp-proxy.ts` | JCS validation partial | Rate limit TODO; unknown methods may pass; tenant field mismatch |
| TS SDK | `core/sdk/typescript/src/index.ts` | Express middleware scaffold | `verifyTrace` → `{ valid: true }`; gRPC client returns `null` |

**Note:** `runtime/sidecar-watcher/src/crypto.rs` implements Ed25519 signing/verification pipeline but it is **not wired** into receipt/cert enforcement paths.

### Ledger (Phase 3 — ledger/architecture agent)

| Dimension | Score | Detail |
|-----------|-------|--------|
| Data model (Prisma) | B | Active schema reasonable |
| Migrations | D | Broken performance migration; duplicate billing SQL; RLS column snake_case mismatch |
| Entry points | F | 3 parallel files (317/324/717 lines); Docker CMD → `index-simple.js`; `package.json start` → `index.js` |
| Type safety | D | 152 `any`; `noImplicitAny: false` in tsconfig |
| Tests | F | 0 `*.test.ts`; `jest --passWithNoTests` |
| MCP layer | C- | Substantial code in `index.ts` only; mock forwarding; `ws` dep missing |

### Architecture fragmentation (Phase 3 — ledger/architecture agent)

| Issue | Detail |
|-------|--------|
| `runtime/` not in root compose | ledger, tool-broker, rag-guard, incident-bot, mpc-fintech, egress-firewall, retrieval-gateway, labeler, attestor, kms-proxy, privacy, wasm-sandbox, sidecar-watcher (partial via services/) |
| Rust crates with Cargo.toml outside workspace | egress-firewall, telemetry-service, mpc-fintech, jwks-manager |
| Unbuildable trees | retrieval-gateway — Rust `main.rs` + Go sources, no manifest |
| Duplicate code | 3 ledger indexes; 2 `epsilon_guard.rs`; 2 VS Code extensions |
| Root Policy.lean | Parallel to `proofs/Policy.lean` — unclear canonical target |

---

## What Works Well (verified non-issues)

1. **Evidence v0.1/v0.2** — schemas, Go implementation, CLI commands, CI smoke workflow
2. **PCS adapter** — `adapters/pcs/` with admission benchmarks
3. **SWE-bench pipeline** — mock engine for CI; real path documented for Linux
4. **Three checked-in examples** with automated pytest (`evidence-basic`, `forensic-replay-basic`, `runtime-evidence-basic`)
5. **Docs build** — `mkdocs build --strict` tracked green
6. **Standards submodules** — initialized and pinned (verified locally 2026-07-02)
7. **Go CLI cmd tests** — pass
8. **Rust workspace tests** (non-excluded crates) — pass on Windows
9. **No hardcoded production secrets** found in audit scans
10. **WASM sandbox** — 2 real tests pass
11. **PF signature signing** — `core/policy-kernel/pf_sig.go` implements Ed25519 sign/verify for cache fast-path (distinct from receipt trust chain)

---

## Remediation PR Stack

| PR | Scope | Findings | Effort |
|----|-------|----------|--------|
| **PR-1: CI honesty** | Fix replay runner CLI (`bash replay_run.sh` arg bug); remove ghost tests; fix `impacted_tests` wiring; drop `passWithNoTests`; audit `continue-on-error` / `\|\| true`; fix SLO Gates lockfile; fix CodeQL artifact upload | F06, F10-F12, F19-F20 | M |
| **PR-2: Trust chain** | Shared Ed25519 verify lib per `docs/specs/dsse-verify-contract.md`; wire into kernel/sidecar/tool-broker/ledger; gate `is_tool_enabled`; document shadow-mode non-prod default | F01-F02, F17, F25 | L |
| **PR-3: Demo/example fixes** | Add `run-demo.ts` or fix script; SDK export alias; fix edge-middleware imports; on-ramps paths | F07-F08, F18 | S |
| **PR-4: Ledger consolidation** | Single entrypoint; fix Dockerfile alignment; add `ws` dep; quarantine broken migrations; real Jest tests | F03-F04, F09, F11, F22, F26-F28 | L |
| **PR-5: Runtime hardening** | Scheduler mutex → `lock().unwrap_or_else(panic)` or `parking_lot`; async log watcher via `spawn_blocking`; regex caching in egress-firewall; un-quarantine sidecar tests | F14-F16, F30-F31, F35 | M |
| **PR-6: Architecture cleanup** | retrieval-gateway manifests or removal; compose profiles for optional services; dedupe epsilon_guard; docs sync; bench baseline refresh | F05, F21, F23-F24, F29, F32, F34 | M |

---

## Methodology and Limitations

### Phases completed

| Phase | Method | Date |
|-------|--------|------|
| 1 — Static scan | Grep, manifest review, workflow read, internal docs, plan file | 2026-07-01 |
| 2 — Runtime verify | `go test`, `cargo test`, submodule check, demo file check, CI inventory (PS equivalent), `gh run list/view --log-failed` | 2026-07-02 (Windows) |
| 3 — Deep dives | Code read: sidecar unwrap/quarantine/async IO/dead_code; trust chain grep; ledger/architecture agent (3 index files, MCP, Prisma, fragmentation) | 2026-07-02 |
| 4 — Backlog | This document | 2026-07-02 |

### Phase 2 commands executed

```text
git submodule status          → CERT-V1 + TRACE-REPLAY-KIT initialized
ls external/                  → CERT-V1, TRACE-REPLAY-KIT, .gitkeep, README.md
cd core/cli/pf && go test ./...  → ok (pf/cmd)
cargo test --workspace --exclude ...  → all included crates pass
Test-Path demos/.../run-demo.ts  → False
CI inventory (67 gated)       → 13 green / 51 red / 3 no_run
gh run list --branch main     → mixed; replay/CERT/SLO/CodeQL failing
gh run view --log-failed      → per-workflow root causes captured above
```

### Not verified this session

- Full `make test` on Linux/WSL
- Native bash `scripts/ci_workflow_inventory.sh` (Windows bash path resolution failed; PS equivalent used)
- Actual latency/throughput benchmarks for sidecar, ledger, egress-firewall
- Every example README command run verbatim
- End-to-end `docker compose up` full platform
- Bench Nightly / Paper Conformance runs still in_progress at query time (2026-07-02T06:02Z) — prior failures triaged instead

### Accuracy rule

Items marked **verified** have a command output or file read backing them. Items marked **suspected** are from static analysis or partial log triage only. No item is marked "broken" without a reproduction step or static proof.

---

## References

- Plan: `.cursor/plans/full_repo_audit_2c4eef77.plan.md` (not edited)
- Internal placeholder inventory: `docs/internal/placeholders/inventory.md`
- CI health matrix: `docs/internal/ci-health-matrix.md`
- Evidence program closure: `docs/roadmap/evidence-program-closure.md`
- DSSE verify contract: `docs/specs/dsse-verify-contract.md`
