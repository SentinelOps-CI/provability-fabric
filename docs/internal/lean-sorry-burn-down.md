# Lean sorry burn-down priority

Priority order for eliminating `sorry` / `by admit` placeholders in Lean proofs. Full elimination across the repo is a long-running effort (F33); CI enforces a **scoped** subset only.

## CI-enforced targets (must be sorry-free)

These paths are checked by `.github/workflows/lean-style.yaml` on every push/PR touching `**/*.lean`:

| Target | Path | Notes |
|--------|------|-------|
| Core DSL | `core/lean-libs/ActionDSL.lean` | Canonical action/budget definitions |
| Budget | `core/lean-libs/Budget.lean` | Budget invariants |
| Invariants | `core/lean-libs/Invariants.lean` | IFC invariants + egress cert lemmas (**expanded 2026-07-03**) |
| Spec template | `spec-templates/v1/proofs/` | Template bundle proofs |
| Example agents | `bundles/my-agent/proofs/Spec.lean` | Reference agent |
| Example agents | `bundles/test-new-user-agent/proofs/Spec.lean` | Reference agent |

The workflow step **Check for 'sorry' or 'by admit' in CI-enforced Lean targets** fails the job if any enforced file contains `sorry` or `by admit`. Research and platform proof trees outside this list may still contain placeholders.

## Out-of-scope sorry inventory (2026-07-17)

| File | `sorry` count | Priority | Rationale |
|------|--------------:|----------|-----------|
| `core/lean-libs/Invariants.lean` | **0** | **P1** | **DONE** — sorry-free; **CI-enforced** as of 2026-07-03 (Wave 7 F33) |
| `proofs/Policy.lean` | **0** | **P2** | **DONE** — `soundness`, `completeness`, `read_requires_label_flow` (role-gated), `ni_bridge` (with label-coherence hypothesis) proved 2026-07-03 |
| `Policy.lean` (repo root) | **0** | **P3** | **DONE** — content-aligned with `proofs/Policy.lean` (2026-07-17); Fabric package mirror for `import Policy` / lean-morph (separate lake packages cannot thin-reexport the same module name) |
| `core/lean-libs/Runtime/MicroInterp.lean` | **0** | **P4** | **DONE (2026-07-18)** — `compileClauses` / `semanticsFromClauses` / `dfa_semantics_match` proved; lake target `Runtime`; string-keyed clause adapter (Extended surface still unfinished) |

**Total outside enforced set:** 0 occurrences in the F33 tracked set (was 24; MicroInterp closed 2026-07-18).

## Burn-down sequence

1. **Align canonical Policy (DONE)** — `proofs/Policy.lean` is source of truth; root `Policy.lean` kept byte-aligned as the Fabric-package mirror (2026-07-17). True thin re-export across lake packages is blocked by duplicate `Policy` module roots.
2. **Invariants.lean (DONE)** — proved 2026-07-02–03: `empty_trace_invariant`, `privacy_budget_additive`, `system_safety`, `plan_validation_preserves_invariants`, `label_flow_preservation`, egress cert namespace (`generateCertificate`, `certificate_integrity`, `policy_hash_verification`, `transitive_non_interference`, `label_flow_monotonicity`, etc.).
3. **proofs/Policy.lean (DONE)** — proved 2026-07-03: `soundness`, `completeness`, role-gated `read_requires_label_flow`, `ni_bridge` with explicit prefix label-coherence hypothesis.
4. **MicroInterp.lean (DONE)** — P4.1–P4.3 landed 2026-07-18: `compileClauses`, `semanticsFromClauses`, proved `dfa_semantics_match` (accept ↔ Mediated) plus `micro_refine_compiled`.
5. **Expand enforced set** — **Invariants.lean added** to `lean-style.yaml` ENFORCED list (2026-07-03). MicroInterp is lake-built and scanned by `lean-offline` smoke; do **not** add it to lean-style ENFORCED until an Extended.Event adapter exists (current clauses are string-keyed).

## MicroInterp P4 — `dfa_semantics_match` (DONE 2026-07-18)

**File:** `core/lean-libs/Runtime/MicroInterp.lean` — theorem `dfa_semantics_match` (**0** `sorry`).

**What landed:**

| Step | Deliverable |
|------|-------------|
| P4.1 | `compileClauses : List ActionClause → DFAM Bool` (forbid-sink automaton) |
| P4.2 | `semanticsFromClauses` with `Checked` ⇔ `forbidEvent = false` |
| P4.3 | `dfa_semantics_match` + supporting lemmas; `lake build Runtime` |

**Follow-ups (non-blocking):** map `ActionDSL.Extended` events into `ActionClause` once Extended compiles; then consider ENFORCED expansion.

**Policy:** Do not weaken lean-style ENFORCED targets. Do not reintroduce `sorry` / `axiom` / `by assumption` vacuous closes.

## Alignment with P16 / burn-down tracker

Placeholder burn-down item **P16** (scoped sorry check) is **DONE**: CI matches enforced targets only. See [placeholders/burn-down.md](placeholders/burn-down.md) LN-006.

Do **not** weaken the enforced-target check to greenwash research sorry debt. Instead, land proofs in priority order and expand enforcement when ready.

## Local verification

```bash
# Same check as lean-style.yaml (from repo root)
ENFORCED="core/lean-libs/ActionDSL.lean core/lean-libs/Budget.lean core/lean-libs/Invariants.lean spec-templates/v1/proofs bundles/my-agent/proofs/Spec.lean bundles/test-new-user-agent/proofs/Spec.lean"
for target in $ENFORCED; do
  find "$target" -name '*.lean' ! -path '*/.lake/*' -exec grep -l 'sorry\|by admit' {} \; 2>/dev/null
done

# Invariants.lean sorry count (informational)
rg -c 'sorry|by admit' core/lean-libs/Invariants.lean

# Full sorry inventory (informational)
rg -c 'sorry|by admit' --glob '*.lean' core/lean-libs proofs Policy.lean
```

Requires Linux, WSL, or Git Bash on Windows (see [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md)).
