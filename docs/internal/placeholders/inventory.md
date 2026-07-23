# Placeholders and Stubs

This document lists places in the repository that use placeholder values, stub implementations, or explicit TODOs for missing behavior. For v1 scope decisions (KMS/Vault, bundle hash, DSSE, SWE-bench, Lean, docs placeholders), see [decisions-v1.md](decisions-v1.md). For removal prompts, proof tests, and status tracking, see [burn-down.md](burn-down.md). It does not list UI input placeholder text, lockfile entries, or legitimate control-flow returns.

**Wave 9+ completion refresh (2026-07-22):** Trust-path DSSE/retrieval closed; tool-broker tenant/risk/throttle/budget **DONE**; ledger MCP rate-limit/counters/hit-rate **DONE**; TS SDK HTTP client + idempotent retry **DONE**; policy-kernel Redis L2 **DONE** (ST-004); LabelerGen/ExportDFA tool polish **DONE** (LN-001/002 — deterministic Lean `hash`, not cryptographic). See [burn-down.md](burn-down.md) and [remediation-tracker.md](../remediation-tracker.md).

---

## 1. Explicit placeholders (string/values)

Historical / already closed in burn-down (PH-001–PH-014). Do not treat these as current blockers unless burn-down status is OPEN.

| Location | Description | Burn-down |
|----------|-------------|-----------|
| `core/cli/pf/main.go` | Bundle hash was placeholder — closed | PH-001 DONE |
| `runtime/sidecar-watcher` test/example hash placeholders | Fixture data only | PH-002/003 DONE |
| `runtime/sidecar-watcher` permit/policy enforcement | DSSE + deny-by-default wired (Waves 2) | PH-004/005 DONE |
| `runtime/retrieval-gateway/src/receipt.rs` | Real DSSE receipts via `pf-dsse`; **crate has `Cargo.toml` and builds in CI** (`retrieval-gateway.yml`) | PH-006 DONE |
| `runtime/mpc-fintech`, ledger rollback, evidence-service, summarize, cert middlewares | Closed or allowlisted per burn-down | PH-007–PH-014 |

---

## 2. Stub implementations (no real logic)

| Location | Description | Burn-down |
|----------|-------------|-----------|
| `bench/swebench/runner.py` | **No stub for openhands:** With `--engine openhands`, the runner checks OpenHands availability at start and exits with a clear error before creating run dirs if not available; it does not emit a stub patch. Only `--engine mock` (or `--mode deterministic`) produces toy outputs (for CI). | ST-001 DONE |
| `runtime/wasm-sandbox` | `scan_for_prohibited_ops` implemented | ST-002 DONE |
| `runtime/sidecar-watcher/src/concurrency.rs` | Pipeline stub closed | ST-003 DONE |
| `core/policy-kernel/cache.go` | Redis L2 get/set/delete/invalidate + sync via `go-redis` + miniredis tests | ST-004 DONE |
| `core/policy-kernel/engine.go` | `verifyReceipt` uses `dsse.VerifyAccessReceipt` (not structural-only) | ST-005 DONE |
| `tools/ci/impacted_only.py` | `--build-impacted` emits `lake build` commands; F12 selector fixed | ST-008 DONE |

---

## 3. TODO / FIXME (unimplemented behavior)

No remaining Wave 9–14 runtime stub rows. Closed under burn-down:

| Location | Reality | Burn-down |
|----------|---------|-----------|
| `runtime/tool-broker` | Tenant fail-closed default; risk from allow-list; throttle sleep; real budget windows | TD-001/002 DONE |
| `runtime/ledger/src/mcp/*` | Sliding-window rate limit + counters + JCS hit-rate | TD-006/007 DONE |
| `core/sdk/typescript` | HTTP client lifecycle + idempotent outbound retry; `verifyTrace` real | TD-009/010/011 DONE |
| `core/sdk/README.md` | Example `// TODO` in Go snippet — allowlisted | TD-015 ALLOWED |

### Closed verify debt (do not re-open)

| Location | Reality |
|----------|---------|
| `runtime/sidecar-watcher/src/broker.rs`, `plan.rs` | `pf_dsse::verify_access_receipt` wired | TD-003/004 DONE |
| `runtime/ledger/src/receipts.ts`, `egress.ts` | DSSE verify via `crypto/dsse` | TD-005/008 DONE |

---

## 4. Lean / proof placeholders

| Location | Description |
|----------|-------------|
| `core/lean-tools/LabelerGen.lean` / `ExportDFA.lean` | Deterministic Lean `hash` / Merkle-style pairing for tool output — **not** cryptographic SHA-256; docs in-source state this. LN-001/002 **DONE**. |
| `proofs/README.md`, `docs/dev/lean-build.md` | Notes on completing `sorry` placeholders |
| `.github/workflows/lean-style.yaml`, `lean-offline.yaml` | Scoped sorry / admit checks for ENFORCED targets (includes Extended + ExtendedAdapter) |
| `tools/proofbot/run.py` | Resolves 'sorry' and 'by admit' placeholders in Lean proofs |

F33 MicroInterp / Runtime lake target closed — see [lean-sorry-burn-down.md](../lean-sorry-burn-down.md). Extended adapter is mathlib-backed; built on `lean-offline-full` (schedule/dispatch), not every-PR smoke.

---

## 5. Adapters / scripts (placeholder logic)

| Location | Description |
|----------|-------------|
| `adapters/dryvr/adapter.sh` | DryVR output parsing placeholder (SC-001 DONE in burn-down) |
| `scripts/db/blue_green_migrate.sh` | Slack webhook URL example `https://hooks.slack.com/services/xxx/yyy/zzz` (allowlisted) |
| ~~tools/pr-bot/README.md~~ | Removed (orphan tool deleted) |

---

## 6. Documentation references

| Location | Description |
|----------|-------------|
| `docs/guides/developer-guide.md` | Recommends removing unused code or implementing stubs to narrow allow(dead_code) |
| `docs/security/signing-rotation.md` | Notes placeholders; integrate with provider and set `CERT_SIGNER_BACKEND=kms|vault` |
| `core/crypto/README.md` | Example with `todo!("SEV verification implementation")` |

---

## 7. Test-only or example stubs

| Location | Note |
|----------|------|
| `runtime/sidecar-watcher/src/main.rs` | Comment: "Synchronous unit test stub…" — not a runtime placeholder |
| `runtime/sidecar-watcher/src/break_glass.rs` | `PostMortemStub` is a real type used in tests |

---

## Summary by area

- **Runtime (sidecar / retrieval / tool-broker):** Trust-path DSSE and broker tenant/risk/throttle/budget **closed**.
- **Ledger MCP:** Rate limiting, counters, and JCS hit-rate **closed**.
- **Core SDK:** `verifyTrace` + HTTP client + idempotent retry **closed** (gRPC deferred by design).
- **Policy-kernel:** Redis L2 on `DecisionCache` + `OptimizedDecisionCache` when `redisAddr` set.
- **Bench / tools:** SWE-bench mock vs OpenHands honesty split; OpenHands eval fail-closed when secrets present.
- **Lean:** ENFORCED includes MicroInterp, Extended, ExtendedAdapter; full Extended lake build on `lean-offline-full` only (T12 ACCEPTED).

Status of record: [burn-down.md](burn-down.md). Live CI counts: [evidence-program-closure.md](../../roadmap/evidence-program-closure.md).
