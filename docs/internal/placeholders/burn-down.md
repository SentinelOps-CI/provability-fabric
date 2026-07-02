# Placeholders and Stubs — v1 Burn-Down Tracker

This document tracks every placeholder value, stub implementation, and TODO-as-behavior that must be removed for v1. It maps each item to:

- **Removal prompt(s):** the exact prompt in the prompt series that owns the fix
- **Proof tests:** concrete tests / CI gates that prove the placeholder is gone and behavior is real
- **Status:** OPEN → IN PROGRESS → DONE, plus PR link(s)
- **Policy exceptions (v1):** Sanitized placeholders are allowed only in explicitly allowlisted docs/scripts examples (e.g., Slack webhook example, `ghp_xxx`) as long as they are variable-style and clearly labeled as examples. Everything else must be eradicated.

See [inventory.md](inventory.md) for the full inventory and [decisions-v1.md](decisions-v1.md) for scope decisions.

**Last updated:** Wave 0 audit reconciliation (2026-07-01). Reset falsely-DONE trust-chain rows per [full-repo-audit-2026-07-01.md](../full-repo-audit-2026-07-01.md) and [remediation-tracker.md](../remediation-tracker.md). Gate `make no-runtime-placeholders` still fails on `build/` artifacts and embedded binary strings; runtime trust stubs remain OPEN.

---

## Prompt → Scope index (quick reference)

| Prompt | Scope / What it removes | Primary proof |
|--------|------------------------|---------------|
| P0 | Baseline scan + generate burn-down checklist | `docs/internal/placeholders/burn-down.md` exists |
| P1 | No-runtime-placeholders gate (strict runtime; allowlisted examples) | `make no-runtime-placeholders` (CI) |
| P2 | Trust root + DSSE verify contract (PEM default; JWKS optional) | cross-lang DSSE verify tests |
| P3 | Cross-language crypto fixtures (Go/Rust/TS) | fixtures + unit tests in each |
| P3.5 | Bundle manifest v1 schema + authority (sidecar/mw) | schema validation + e2e deny mismatch |
| P4 | CLI bundle digest + manifest outputs (remove "placeholder-hash") | CLI integration tests |
| P5 | Evidence-service: file signer + plugin interface + real compliance artifacts | service tests + artifact content tests |
| P6 | Sidecar-watcher: strict plan sig + manifest digests + remove return true stubs + real concurrency | cargo tests + integration tests |
| P7 | Tool-broker: tenant/risk/throttle/sig verify | cargo tests |
| P8 | Retrieval-gateway: real DSSE receipts (no placeholder key) | receipt DSSE tests |
| P9 | Ledger: signature verify + rate limiting + counters + hit-rate tracking | TS tests (fake timers + crypto fixtures) |
| P10 | Policy-kernel: Redis cache + sig verification | go tests + miniredis |
| P11 | Cert middlewares: manifest-driven context + trust root wiring | adapter tests (Go/Py/TS) |
| P12 | SWE-bench: solver-disabled mode (no fake patch stubs) | pytest runner tests |
| P13 | wasm-sandbox: real scan_for_prohibited_ops | wasm scan tests |
| P14 | tools/ci/impacted_only.py: build impacted proofs | pytest unit tests |
| P15 | create-sentinel-app: real replay integration | node smoke test |
| P16 | Lean: restrict "no sorry" checks to CI-enforced targets | lean CI passes + scoped sorry check |

**Add-on prompts (not in main series):**

| Prompt | Scope |
|--------|--------|
| P4.1 | Tools/results summarizer: real bundle_id/signature/replay_drift from artifacts |
| P4.2 | CLI revoke: revoked_by auth context (real, tested) |
| P7.1 | MPC fintech compliance validators: real validation or typed deny (no placeholder acceptance) |
| P9.1 | Ledger migrations: remove rollback_checksum_placeholder (derive or remove) |
| P11.1 | TypeScript SDK: gRPC client, trace verify, connection lifecycle, retry (removes SDK TODOs) |
| P13.1 | core/crypto wasm_pool: eliminate placeholder return path + deterministic tests |
| P17 | VSCode extension: real webview comms |
| P18 | DryVR adapter: real parsing + tests |

---

## Global proofs (apply to every row)

Every item marked DONE must satisfy:

1. **Gate proof:** `make no-runtime-placeholders` passes (P1), unless the row is explicitly "Allowed example placeholder".
2. **Behavior proof:** At least one targeted test listed in the row passes.
3. **Regression proof:** A test exists that would have failed before the fix (or the gate would have failed).

---

## 1. Explicit placeholders (literal values)

**Status legend:** OPEN | IN PROGRESS | DONE | ALLOWED (EXAMPLE)  
**Audit:** finding ID(s) from [full-repo-audit-2026-07-01.md](../full-repo-audit-2026-07-01.md) when OPEN due to reconciliation  
**PR:** link or TBD  
**Owner:** team/area (runtime, core, services, adapters, tools, lean, bench)

| ID | Location | Placeholder | Removal prompt(s) | Proof tests (must exist) | Owner | Status | Audit | PR |
|----|----------|-------------|-------------------|--------------------------|-------|--------|-------|-----|
| PH-001 | core/cli/pf/main.go | BundleHash: "placeholder-hash" | P4 | go test ./core/cli/pf/... -run TestBundleDigestFromBytes + make no-runtime-placeholders | core/cli | DONE | — | TBD |
| PH-002 | runtime/sidecar-watcher/src/main.rs | *_hash_placeholder, attestation_*_placeholder in test/example data | P6 (+ P3.5 manifest wiring) | cargo test -p sidecar-watcher (fixture-based plan + manifest load) + gate | runtime/sidecar | DONE | — | TBD |
| PH-003 | runtime/sidecar-watcher/src/revocation.rs | policy_hash_placeholder, dfa_hash_placeholder, labeler_hash_placeholder | P6 | cargo test -p sidecar-watcher -- revocation + gate | runtime/sidecar | DONE | — | TBD |
| PH-004 | runtime/sidecar-watcher/src/permit_enforcement.rs | CERT_SIG unconfigured fallback; no real DSSE verify | P6 (+ P2 trust root/DSSE) | cargo test -p sidecar-watcher -- dsse_verification + gate | runtime/sidecar | OPEN | F01, F02 | TBD |
| PH-005 | runtime/sidecar-watcher/src/policy_adapter.rs + permit_enforcement.rs | Shadow mode always allows; `is_tool_enabled` default true | P6 | cargo test -p sidecar-watcher -- policy_checks_deny_by_default + gate | runtime/sidecar | OPEN | F02, F25 | TBD |
| PH-006 | runtime/retrieval-gateway/src/receipt.rs | env signing key; crate unbuildable (no Cargo.toml) | P8 (+ P2/P3 fixtures) | cargo test -p retrieval-gateway -- receipt_dsse + gate | runtime/retrieval | OPEN | F05 | TBD |
| PH-007 | runtime/mpc-fintech/src/compliance.rs | placeholder validation branches | P7.1 | cargo test -p mpc-fintech -- compliance_validation + gate | runtime/mpc | DONE | TBD |
| PH-008 | runtime/ledger/prisma/migrations/.../rollback.sql | rollback_checksum_placeholder | P9.1 | migration snapshot test or schema lint + gate | runtime/ledger | DONE | TBD |
| PH-009 | services/evidence-service/main.go | kms/vault "not implemented"; placeholder compliance files | P5 | go test ./services/evidence-service/... + artifact content test + gate | services/evidence | DONE | TBD |
| PH-010 | tools/results/summarize.py | bundle_id/signature/replay_drift placeholders | P4.1 | python -m pytest tools/results/test_summarize.py + gate | tools/results | DONE | TBD |
| PH-011 | tools/results/summarize.bat | same placeholders | P4.1 | Windows CI smoke for summarize + gate | tools/results | DONE | TBD |
| PH-012 | adapters/gochi-cert-middleware/middleware.go | policy_hash/proof_hash/automata_hash/labeler_hash: "placeholder-*" | P11 (+ P3.5) | go test ./adapters/gochi-cert-middleware/... + gate | adapters/go | DONE | TBD |
| PH-013 | adapters/fastapi_cert_middleware/__init__.py | placeholder hashes | P11 (+ P3.5) | pytest adapters/fastapi_cert_middleware + gate | adapters/python | DONE | TBD |
| PH-014 | adapters/express-cert-middleware/index.ts | placeholder hashes | P11 (+ P3.5) | pnpm -w test adapters/express-cert-middleware + gate | adapters/ts | DONE | TBD |

---

## 2. Stub implementations (no real logic)

| ID | Location | Stub | Removal prompt(s) | Proof tests | Owner | Status | Audit | PR |
|----|----------|------|-------------------|-------------|-------|--------|-------|-----|
| ST-001 | bench/swebench/runner.py | stub patch engine _stub_* | P12 | pytest bench/swebench/test_runner.py::test_solver_disabled_mode + gate | bench | DONE | TBD |
| ST-002 | runtime/wasm-sandbox/README.md + impl | scan_for_prohibited_ops documented as stub | P13 | cargo test -p wasm-sandbox -- scan_prohibited_ops + gate | runtime/wasm | DONE | TBD |
| ST-003 | runtime/sidecar-watcher/src/concurrency.rs | placeholder event processing | P6 | cargo test -p sidecar-watcher -- concurrency_pipeline + gate | runtime/sidecar | DONE | TBD |
| ST-004 | core/policy-kernel/cache.go | Redis sync + ops placeholder/TODO | P10 | go test ./core/policy-kernel/... -run TestRedisCache* + gate | core/policy | DONE | TBD |
| ST-005 | core/policy-kernel/engine.go | signature verification structural-only (`verifyReceipt` returns nil) | P10 | go test ./core/policy-kernel/... -run TestSignatureVerification* + gate | core/policy | OPEN | F01 | TBD |
| ST-006 | core/cli/pf/platform_commands.go | aggregation stub | P4 | go test ./core/cli/pf/... -run TestPlatformAggregationReport + gate | core/cli | DONE | TBD |
| ST-007 | core/crypto/wasm_pool.rs | one path returns placeholder | P13.1 | cargo test -p core-crypto -- wasm_pool + gate | core/crypto | DONE | TBD |
| ST-008 | tools/ci/impacted_only.py | `--build-impacted` logs only; no lake build execution | P14 | pytest tools/ci/test_impacted_only.py + gate | tools/ci | OPEN | F12 | TBD |

---

## 3. TODO / FIXME (unimplemented behavior in runtime paths)

| ID | Location | TODO behavior | Removal prompt(s) | Proof tests | Owner | Status | Audit | PR |
|----|----------|---------------|-------------------|-------------|-------|--------|-------|-----|
| TD-001 | runtime/tool-broker/src/main.rs | tenant/risk/throttling/sig verify (structural-only receipt check) | P7 | cargo test -p tool-broker (tenant + throttle + sig) + gate | runtime/broker | OPEN | F01 | TBD |
| TD-002 | runtime/tool-broker/src/ratelimit.rs | budget tracking TODO | P7 | cargo test -p tool-broker -- ratelimit + gate | runtime/broker | OPEN | F01 | TBD |
| TD-003 | runtime/sidecar-watcher/src/broker.rs | sig verification structural-only | P6 | cargo test -p sidecar-watcher -- plan_sig_strict + gate | runtime/sidecar | OPEN | F01 | TBD |
| TD-004 | runtime/sidecar-watcher/src/plan.rs | sig verification structural-only | P6 | same as above + "CI forbids insecure" test | runtime/sidecar | OPEN | F01 | TBD |
| TD-005 | runtime/ledger/src/receipts.ts | Ed25519 verify TODO (length/alg check only) | P9 | pnpm -w test runtime/ledger -- receipts_verify + gate | runtime/ledger | OPEN | F01, F11 | TBD |
| TD-006 | runtime/ledger/src/mcp/mcp-proxy.ts | proper rate limiting + counters TODO | P9 | TS tests w/ fake timers + gate | runtime/ledger | OPEN | F04, F11 | TBD |
| TD-007 | runtime/ledger/src/mcp/jcs-validator.ts | hit-rate tracking TODO | P9 | TS tests + gate | runtime/ledger | OPEN | F11 | TBD |
| TD-008 | runtime/ledger/src/egress.ts | signature verification TODO | P9 | TS tests + gate | runtime/ledger | OPEN | F01 | TBD |
| TD-009 | core/sdk/typescript/src/index.ts | gRPC client null; trace verify returns `{ valid: true }` | P11.1 | pnpm -w test core/sdk/typescript + gate | core/sdk | OPEN | F17, F18 | TBD |
| TD-010 | core/sdk/typescript/src/client.ts | connection logic TODO | P11.1 | same | core/sdk | OPEN | F17 | TBD |
| TD-011 | core/sdk/typescript/src/middleware/express.ts | retry logic TODO | P11.1 | same | core/sdk | OPEN | F17 | TBD |
| TD-012 | core/cli/pf/src/revoke.rs | revoked_by auth context TODO | P4.2 | go test ./core/cli/pf/... -run TestRevokeAuthContext + gate | core/cli | DONE | TBD |
| TD-013 | vscode-extension/src/extension.ts | webview comms TODO | P17 | pnpm test vscode-extension (or npm) + gate | tooling/vscode | DONE | TBD |
| TD-014 | tools/create-sentinel-app/index.js | replay is echo "todo" | P15 | node smoke test for generated app + gate | tools/scaffold | DONE | TBD |
| TD-015 | core/sdk/README.md | example // TODO | (doc-only; allow if clearly example) | n/a (doc allowlist) | docs | ALLOWED (EXAMPLE) | n/a |

---

## 4. Lean / proof placeholders

**Policy (v1):** Zero sorry/by admit only in CI-enforced Lean targets; research dirs may contain sorry if excluded from checks.

| ID | Location | Placeholder | Removal prompt(s) | Proof tests | Owner | Status | PR |
|----|----------|-------------|-------------------|-------------|-------|--------|-----|
| LN-001 | core/lean-tools/LabelerGen.lean | placeholder returns | P16 (+ P16.1 if enforced target) | lake build for enforced targets + scoped sorry check | lean | DONE | TBD |
| LN-002 | core/lean-tools/ExportDFA.lean | placeholder hash | P16 + P16.1 if enforced | same | lean | DONE | TBD |
| LN-003 | core/lean-libs/ExportDFA.lean | "SHA-256 impl placeholder" | P16 + P16.1 if enforced | same | lean | DONE | TBD |
| LN-004 | proofs/README.md | notes about sorry | P16 (scope only; allowed if excluded) | scoped sorry check must ignore this dir | docs/lean | DONE | TBD |
| LN-005 | docs/dev/lean-build.md | placeholder proofs mention | P16 (scope only) | scoped sorry check | docs/lean | DONE | TBD |
| LN-006 | .github/workflows/lean-style.yaml | global sorry scan too strict | P16 | CI passes; scoped scan matches enforced targets | lean | DONE | TBD |
| LN-007 | .github/workflows/lean-offline.yaml | same | P16 | CI passes; scoped scan | lean | DONE | TBD |
| LN-008 | tools/proofbot/run.py | references placeholder resolution | P16 | proofbot tests (if any) or CI non-required | tools/lean | DONE | TBD |

---

## 5. Adapters / scripts (placeholder logic)

Mostly example placeholders. v1 policy: allowed if variable-style and clearly labeled.

| ID | Location | Placeholder | Removal prompt(s) | Proof tests | Owner | Status | PR |
|----|----------|-------------|-------------------|-------------|-------|--------|-----|
| SC-001 | adapters/dryvr/adapter.sh | placeholder parsing | P18 | shell test harness or integration test with fixture output + gate | adapters/dryvr | DONE | TBD |
| SC-002 | scripts/db/blue_green_migrate.sh | Slack webhook xxx/yyy/zzz | Allowlisted example | make no-runtime-placeholders must allow this file | scripts | ALLOWED (EXAMPLE) | n/a |
| SC-003 | tools/pr-bot/README.md | example token | Allowlisted example | same | docs/tools | ALLOWED (EXAMPLE) | n/a |

---

## 6. Bench / tools stubs (non-runtime but must be honest)

| ID | Location | Stub/placeholder | Removal prompt(s) | Proof tests | Owner | Status | PR |
|----|----------|------------------|-------------------|-------------|-------|--------|-----|
| BT-001 | tools/results/summarize.py + .bat | placeholder fields | P4.1 | pytest + Windows smoke + gate | tools | DONE | TBD |
| BT-002 | api/v1/BUF_USAGE.md | suggests adding stub generation | doc-only | n/a | docs | ALLOWED (DOC) | n/a |

---

## 7. Test-only / example stubs (not blockers)

These are not unimplemented behavior and should remain as-is unless they trip gates incorrectly.

| ID | Location | Note | Action |
|----|----------|------|--------|
| EX-001 | runtime/sidecar-watcher/src/main.rs | comment: "Synchronous unit test stub…" | Ensure gate does not flag benign comments unless policy says so |
| EX-002 | runtime/sidecar-watcher/src/break_glass.rs | PostMortemStub is a real type used in tests | Not a placeholder; keep |

---

## Required add-on prompts (to complete eradication)

To ensure "no placeholders remain" is actually true, the following add-on prompts must be added to the series:

| Prompt | Description |
|--------|-------------|
| P4.1 | Tools/results summarizer: replace placeholder bundle_id/signature/replay_drift with real values derived from actual artifacts |
| P4.2 | CLI revoke: implement revoked_by auth context (even if v1 is "local identity", make it real and test it) |
| P7.1 | MPC fintech compliance validators: implement real validation branches or explicit deny with typed reasons (no placeholder acceptance) |
| P9.1 | Ledger migrations: remove rollback_checksum_placeholder by generating/deriving the correct value or removing dependency |
| P11.1 | TypeScript SDK completion: gRPC client, trace verification, connection lifecycle, retry logic (removes all SDK TODOs) |
| P13.1 | core/crypto wasm_pool: eliminate placeholder return path; add deterministic tests |
| P17 | VSCode extension webview comms: implement real message passing + tests |
| P18 | DryVR adapter parsing: implement real parsing + tests |

---

## How to close an item (definition of DONE)

A row can move to DONE only when:

1. **Gate:** `make no-runtime-placeholders` passes (P1).
2. **Targeted tests:** The row's "Proof tests" pass.
3. **Evidence:** The placeholder string/stub/TODO-as-behavior is removed or replaced with real logic.
4. **Docs:** Update this file (set status to DONE and add PR link).

---

## Suggested workflow for the team

1. Run P0 and ensure this file reflects current reality.
2. Land P1 early (scoped), so regressions are impossible.
3. Land P2/P3 (trust + crypto fixtures), then P3.5/P4 (manifest + CLI), then P6/P8/P11 (sidecar/receipts/middlewares).
4. Use this burn-down as the PR checklist: every PR must close at least one ID.
