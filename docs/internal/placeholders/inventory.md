# Placeholders and Stubs

This document lists places in the repository that use placeholder values, stub implementations, or explicit TODOs for missing behavior. For v1 scope decisions (KMS/Vault, bundle hash, DSSE, SWE-bench, Lean, docs placeholders), see [decisions-v1.md](decisions-v1.md). For removal prompts, proof tests, and status tracking, see [burn-down.md](burn-down.md). It does not list UI input placeholder text, lockfile entries, or legitimate control-flow returns.

**Wave 0 reconciliation (2026-07-01):** Trust-chain rows reset to OPEN in [burn-down.md](burn-down.md) per [full-repo-audit-2026-07-01.md](../full-repo-audit-2026-07-01.md). Runtime source no longer contains `dsse:placeholder` or `vec![0u8; 32]` signing keys; structural-only signature verification and permissive enforcement remain.

---

## 1. Explicit placeholders (string/values)

| Location | Description |
|----------|-------------|
| `core/cli/pf/main.go` | `BundleHash: "placeholder-hash"` (bundle hash not calculated from actual bundle) |
| `runtime/sidecar-watcher/src/main.rs` | `plan_hash_placeholder`, `policy_hash_placeholder`, `automata_hash_placeholder`, `labeler_hash_placeholder`, `ni_monitor_hash_placeholder`, `resource_placeholder`, `attestation_token_placeholder`, `attestation_sig_placeholder` in test/example data |
| `runtime/sidecar-watcher/src/revocation.rs` | `policy_hash_placeholder`, `dfa_hash_placeholder`, `labeler_hash_placeholder` (would be actual hashes) |
| `runtime/sidecar-watcher/src/permit_enforcement.rs` | `CERT_SIG` from env or unconfigured; `is_tool_enabled` defaults true (manifest allowlist not wired) |
| `runtime/sidecar-watcher/src/policy_adapter.rs` | Shadow mode always allows; path/label checks simulated |
| `runtime/retrieval-gateway/src/receipt.rs` | Signing key from env; **no Cargo.toml** — crate unbuildable (F05) |
| `runtime/mpc-fintech/src/compliance.rs` | "Placeholder implementations for other validation types" |
| `runtime/ledger/prisma/migrations/.../rollback.sql` | `'rollback_checksum_placeholder'` |
| `services/evidence-service/main.go` | kms/vault signers: "not implemented"; placeholder compliance files `audit-proof.json`, `conformance.md` |
| `tools/results/summarize.py` | `bundle_id`: `"placeholder-sha256-digest"`, `signature`: `"placeholder"`, `replay_drift`: `"placeholder"` |
| `tools/results/summarize.bat` | Same placeholders in generated `results.json` |
| `adapters/gochi-cert-middleware/middleware.go` | `policy_hash`, `proof_hash`, `automata_hash`, `labeler_hash`: `"placeholder-*-hash"` |
| `adapters/fastapi_cert_middleware/__init__.py` | Same placeholder hashes in cert context |
| `adapters/express-cert-middleware/index.ts` | Same placeholder hashes in cert context |

---

## 2. Stub implementations (no real logic)

| Location | Description |
|----------|-------------|
| `bench/swebench/runner.py` | **No stub for openhands:** With `--engine openhands`, the runner checks OpenHands availability at start and exits with a clear error before creating run dirs if not available; it does not emit a stub patch. Only `--engine mock` (or `--mode deterministic`) produces toy outputs (for CI). The rest of the pipeline (evidence, replay bundle, policy hash, proof hook, cost report, PF metadata sidecar, patch apply check, engine_mode/engine_success/engine_error in metadata; guarded evidence and policy_compliance_summary written unconditionally) is implemented. On native Windows only mock/deterministic are allowed; for real OpenHands run from WSL or Linux. |
| `bench/swebench/README.md` | Documents the full runner: OpenHands must be installed for `--engine openhands` (run exits otherwise); policy pack, replay, proof hook, cost accounting, PF metadata sidecar, patch apply check, and PF-guarded evidence (run_started, policy_compliance_summary always) are implemented. Includes a "Windows and OpenHands" note (fcntl, WSL workaround). |
| `runtime/wasm-sandbox/README.md` | Documents that `scan_for_prohibited_ops` is a stub (returns empty) |
| `runtime/sidecar-watcher/src/concurrency.rs` | "Process event (placeholder - would call actual processing logic)"; "Process individual event (placeholder)" |
| `core/policy-kernel/cache.go` | "This is a placeholder for Redis synchronization logic"; Redis get/set/delete/close "not implemented" / "TODO" |
| `core/policy-kernel/engine.go` | `verifyReceipt` structural validation only; returns nil without Ed25519 verify |
| `core/cli/pf/platform_commands.go` | "Simple aggregation stub; in production call a report generator script" |
| `core/crypto/wasm_pool.rs` | "For now, return a placeholder" (in some path) |
| `api/v1/BUF_USAGE.md` | Suggests adding buf.gen.yaml to generate stubs for Go/TypeScript |
| `tools/ci/impacted_only.py` | `--build-impacted` logs guidance only; does not run `lake build` |

---

## 3. TODO / FIXME (unimplemented behavior)

| Location | Description |
|----------|-------------|
| `runtime/tool-broker/src/main.rs` | TODO: Extract tenant from plan/context; TODO: Calculate risk from tool/context; TODO: Implement throttling; TODO: Implement actual signature verification |
| `runtime/tool-broker/src/ratelimit.rs` | TODO: Implement budget tracking |
| `runtime/sidecar-watcher/src/broker.rs` | TODO: Implement actual signature verification |
| `runtime/sidecar-watcher/src/plan.rs` | TODO: Implement actual signature verification |
| `runtime/ledger/src/receipts.ts` | TODO: Implement actual Ed25519 signature verification |
| `runtime/ledger/src/mcp/mcp-proxy.ts` | TODO: Implement proper rate limiting with sliding window; TODO: Implement counters |
| `runtime/ledger/src/mcp/jcs-validator.ts` | TODO: Implement hit rate tracking |
| `runtime/ledger/src/egress.ts` | TODO: Implement actual signature verification |
| `core/sdk/typescript/src/index.ts` | TODO: Implement gRPC client (returns null); TODO: Implement trace verification |
| `core/sdk/typescript/src/client.ts` | TODO: Implement connection/disconnection logic |
| `core/sdk/typescript/src/middleware/express.ts` | TODO: Implement actual retry logic |
| `core/policy-kernel/cache.go` | TODOs: Initialize Redis client; implement Redis deletion/close/get/set when client available |
| `core/cli/pf/src/revoke.rs` | TODO: Get revoked_by from auth context (uses "cli-user") |
| `vscode-extension/src/extension.ts` | Comment: "This would need to be implemented with proper webview communication" |
| `tools/create-sentinel-app/index.js` | replay script is `'echo "todo"'` |
| `core/sdk/README.md` | Example: `// TODO: Implement actual client` |

---

## 4. Lean / proof placeholders

| Location | Description |
|----------|-------------|
| `core/lean-tools/LabelerGen.lean` | "For now, return a placeholder" (two places) |
| `core/lean-tools/ExportDFA.lean` | "For now, return a placeholder hash" |
| `core/lean-libs/ExportDFA.lean` | "Simple SHA-256 implementation (placeholder for now)" |
| `proofs/README.md` | Notes on completing `sorry` placeholders with detailed proofs |
| `docs/dev/lean-build.md` | Documents "Placeholder Proofs" and replacing them |
| `.github/workflows/lean-style.yaml` | Checks for placeholder proofs (sorry / by admit) |
| `.github/workflows/lean-offline.yaml` | Same check |
| `tools/proofbot/run.py` | Resolves 'sorry' and 'by admit' placeholders in Lean proofs |

---

## 5. Adapters / scripts (placeholder logic)

| Location | Description |
|----------|-------------|
| `adapters/dryvr/adapter.sh` | "This is a placeholder - actual parsing would depend on DryVR's output format" (two places) |
| `scripts/db/blue_green_migrate.sh` | Slack webhook URL example `https://hooks.slack.com/services/xxx/yyy/zzz` |
| `tools/pr-bot/README.md` | Example token `ghp_xxxxxxxxxxxx` |

---

## 6. Documentation references

| Location | Description |
|----------|-------------|
| `docs/guides/developer-guide.md` | Recommends removing unused code or implementing stubs to narrow allow(dead_code); suggests `// TODO(issue-N):` in comments |
| `docs/security/signing-rotation.md` | Notes placeholders; integrate with provider and set `CERT_SIGNER_BACKEND=kms|vault` |
| `core/crypto/README.md` | Example with `todo!("SEV verification implementation")` |

---

## 7. Test-only or example stubs

| Location | Description |
|----------|-------------|
| `runtime/sidecar-watcher/src/main.rs` | Comment: "Synchronous unit test stub: do not run in normal builds" |
| `runtime/sidecar-watcher/src/break_glass.rs` | `PostMortemStub` is an implemented type used for break-glass post-mortem; tests in `tests/break_glass_mechanism.rs` and workflow `paper-conformance.yaml` run `test_break_glass_post_mortem_stub_emission` |

---

## Summary by area

- **Runtime (sidecar-watcher):** Most placeholder hashes and "return true" stubs live here (main, policy_adapter, permit_enforcement, revocation, concurrency).
- **Core (policy-kernel, CLI, SDK, crypto):** Redis/cache stubs, signature verification TODOs, aggregation stub, wasm_pool placeholder, TypeScript SDK TODOs.
- **Services:** evidence-service kms/vault signers and placeholder compliance files.
- **Adapters:** Cert middlewares (Go, Python, TS) use placeholder hashes; DryVR adapter has placeholder parsing.
- **Bench / tools:** SWE-bench runner exits before creating run dirs if OpenHands is unavailable (no stub); only `--engine mock` or `--mode deterministic` produce toy outputs. Full evidence pipeline (replay bundle, policy hash, proof hook, cost report, PF metadata sidecar, patch apply check, guarded evidence) is implemented. Summarize scripts; proofbot/Lean placeholder handling; impacted_only "not yet implemented."
- **Lean/proofs:** Placeholder implementations in Lean and docs/CI that check for proof placeholders.

Use this list to prioritize replacing stubs with real implementations or to track technical debt.
