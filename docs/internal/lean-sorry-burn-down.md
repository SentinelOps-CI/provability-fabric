# Lean sorry burn-down priority

Priority order for eliminating `sorry` / `by admit` placeholders in Lean proofs. Full elimination across the repo is a long-running effort (F33); CI enforces a **scoped** subset only.

## CI-enforced targets (must be sorry-free)

These paths are checked by `.github/workflows/lean-style.yaml` on every push/PR touching `**/*.lean`, and by `.github/workflows/lean-offline.yaml` smoke on the same ENFORCED set:

| Target | Path | Notes |
|--------|------|-------|
| Core DSL | `core/lean-libs/ActionDSL.lean` | Canonical action/budget definitions |
| Budget | `core/lean-libs/Budget.lean` | Budget invariants |
| Invariants | `core/lean-libs/Invariants.lean` | IFC invariants + egress cert lemmas (**expanded 2026-07-03**) |
| MicroInterp | `core/lean-libs/Runtime/MicroInterp.lean` | DFA↔semantics coupling (**ENFORCED 2026-07-22**, Wave 12.2) |
| Spec template | `spec-templates/v1/proofs/` | Template bundle proofs |
| Example agents | `bundles/my-agent/proofs/Spec.lean` | Reference agent |
| Example agents | `bundles/test-new-user-agent/proofs/Spec.lean` | Reference agent |

The workflow step **Check for 'sorry' or 'by admit' in CI-enforced Lean targets** fails the job if any enforced file contains `sorry` or `by admit`. Research and platform proof trees outside this list may still contain placeholders.

`ActionDSL.Extended` and `Runtime.ExtendedAdapter` compile under vendored mathlib (`lake build` / lean-style / lean-offline-full) but stay off the every-PR mathlib-free smoke path; smoke still compiles `Runtime.MicroInterp` with bare `lean` (no mathlib import).

## Out-of-scope sorry inventory (2026-07-22)

| File | `sorry` count | Priority | Rationale |
|------|--------------:|----------|-----------|
| `core/lean-libs/Invariants.lean` | **0** | **P1** | **DONE** — sorry-free; **CI-enforced** as of 2026-07-03 (Wave 7 F33) |
| `proofs/Policy.lean` | **0** | **P2** | **DONE** — `soundness`, `completeness`, `read_requires_label_flow` (role-gated), `ni_bridge` (with label-coherence hypothesis) proved 2026-07-03; **sole** Policy module (root mirror removed 2026-07-22) |
| `core/lean-libs/Runtime/MicroInterp.lean` | **0** | **P4** | **DONE (2026-07-18)** — `compileClauses` / `semanticsFromClauses` / `dfa_semantics_match` proved; **lean-style + lean-offline ENFORCED** as of Wave 12.2 (2026-07-22) |
| `core/lean-libs/ActionDSL/Extended.lean` | **0** | **P4.1** | **DONE (2026-07-22)** — lake root `ActionDSL.Extended`; reserved-name / BEq fixes under vendored mathlib |
| `core/lean-libs/Runtime/ExtendedAdapter.lean` | **0** | **P4.1** | **DONE (2026-07-22)** — `eventLabel` / `toMicroClause` + bridge lemmas (`eventLabel_eq_of_eventMatches`, `dfa_semantics_match_extended`) |

**Total outside enforced set:** 0 occurrences in the F33 tracked set (was 24; MicroInterp closed 2026-07-18; Extended adapter closed 2026-07-22).

## Burn-down sequence

1. **Canonical Policy (DONE)** — `proofs/Policy.lean` is the only Policy module; root `Policy.lean` mirror removed. Root `Fabric.lean` is a Lake package marker only.
2. **Invariants.lean (DONE)** — proved 2026-07-02–03: `empty_trace_invariant`, `privacy_budget_additive`, `system_safety`, `plan_validation_preserves_invariants`, `label_flow_preservation`, egress cert namespace (`generateCertificate`, `certificate_integrity`, `policy_hash_verification`, `transitive_non_interference`, `label_flow_monotonicity`, etc.).
3. **proofs/Policy.lean (DONE)** — proved 2026-07-03: `soundness`, `completeness`, role-gated `read_requires_label_flow`, `ni_bridge` with explicit prefix label-coherence hypothesis.
4. **MicroInterp.lean (DONE)** — P4.1–P4.3 landed 2026-07-18: `compileClauses`, `semanticsFromClauses`, proved `dfa_semantics_match` (accept ↔ Mediated) plus `micro_refine_compiled`.
5. **Expand enforced set (DONE Wave 12.2)** — **Invariants.lean** added 2026-07-03; **MicroInterp.lean** added to lean-style / lean-offline ENFORCED 2026-07-22 after Extended.Event adapter landed. Full mathlib `lake build` remains Monday/dispatch (`lean-offline-full`), not every PR.

## MicroInterp P4 — `dfa_semantics_match` (DONE 2026-07-18)

**File:** `core/lean-libs/Runtime/MicroInterp.lean` — theorem `dfa_semantics_match` (**0** `sorry`).

**What landed:**

| Step | Deliverable |
|------|-------------|
| P4.1 | `compileClauses : List ActionClause → DFAM Bool` (forbid-sink automaton) |
| P4.2 | `semanticsFromClauses` with `Checked` ⇔ `forbidEvent = false` |
| P4.3 | `dfa_semantics_match` + supporting lemmas; `lake build Runtime` |

**Extended adapter (DONE 2026-07-22):** `Runtime/ExtendedAdapter.lean` maps `PF.ActionDSL.Event` → MicroInterp string keys / `ActionClause`; bridge lemmas reuse `dfa_semantics_match` on `toMicroClauses`.

**Policy:** Do not weaken lean-style ENFORCED targets. Do not reintroduce `sorry` / `axiom` / `by assumption` vacuous closes. Do not put full mathlib offline on every PR.

## Alignment with P16 / burn-down tracker

Placeholder burn-down item **P16** (scoped sorry check) is **DONE**: CI matches enforced targets only. See [placeholders/burn-down.md](placeholders/burn-down.md) LN-006.

Do **not** weaken the enforced-target check to greenwash research sorry debt. Instead, land proofs in priority order and expand enforcement when ready.

## Local verification

```bash
# Same check as lean-style.yaml (from repo root)
ENFORCED="core/lean-libs/ActionDSL.lean core/lean-libs/ActionDSL/Extended.lean core/lean-libs/Budget.lean core/lean-libs/Invariants.lean core/lean-libs/Runtime/MicroInterp.lean core/lean-libs/Runtime/ExtendedAdapter.lean spec-templates/v1/proofs bundles/my-agent/proofs/Spec.lean bundles/test-new-user-agent/proofs/Spec.lean"
for target in $ENFORCED; do
  find "$target" -name '*.lean' ! -path '*/.lake/*' -exec grep -l 'sorry\|by admit' {} \; 2>/dev/null
done

# MicroInterp bare compile (lean-offline-smoke; no mathlib)
(cd core/lean-libs && lean Runtime/MicroInterp.lean)

# Extended + adapter under vendored mathlib (lean-style / lean-offline-full)
(cd core/lean-libs && lake build ActionDSL.Extended Runtime.ExtendedAdapter)

# Invariants.lean sorry count (informational)
rg -c 'sorry|by admit' core/lean-libs/Invariants.lean

# Full sorry inventory (informational)
rg -c 'sorry|by admit' --glob '*.lean' core/lean-libs proofs
```

Requires Linux, WSL, or Git Bash on Windows (see [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md)).
