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
| `core/lean-libs/Runtime/MicroInterp.lean` | 2 | **P4** | Runtime micro-interpreter; not in enforced set; `dfa_semantics_match` both directions blocked on DFA↔semantics generator (see MicroInterp P4 section below) |

**Total outside enforced set:** 2 occurrences (was 24; **22 eliminated** through Invariants + Policy tree F33 burn-down through 2026-07-17).

## Burn-down sequence

1. **Align canonical Policy (DONE)** — `proofs/Policy.lean` is source of truth; root `Policy.lean` kept byte-aligned as the Fabric-package mirror (2026-07-17). True thin re-export across lake packages is blocked by duplicate `Policy` module roots.
2. **Invariants.lean (DONE)** — proved 2026-07-02–03: `empty_trace_invariant`, `privacy_budget_additive`, `system_safety`, `plan_validation_preserves_invariants`, `label_flow_preservation`, egress cert namespace (`generateCertificate`, `certificate_integrity`, `policy_hash_verification`, `transitive_non_interference`, `label_flow_monotonicity`, etc.).
3. **proofs/Policy.lean (DONE)** — proved 2026-07-03: `soundness`, `completeness`, role-gated `read_requires_label_flow`, `ni_bridge` with explicit prefix label-coherence hypothesis.
4. **MicroInterp.lean (2 sorry, PARTIAL)** — see P4 section; not tractable without a formalized DFA generator coupling.
5. **Expand enforced set** — **Invariants.lean added** to `lean-style.yaml` ENFORCED list (2026-07-03); do **not** add MicroInterp until its 2 sorry are gone.

## MicroInterp P4 — `dfa_semantics_match` (blocked)

**File:** `core/lean-libs/Runtime/MicroInterp.lean` — theorem `dfa_semantics_match` (two `sorry`, accept⇒witness and witness⇒accept).

**Why not proved (2026-07-17):** Hypotheses only supply unconstrained `clauses`, `M : DFAM`, and `sem : Semantics`. There is no Lean `compileClauses` (or sidecar ActionDSL→DFA export) that ties `accepts M` to `sem.Checked`. Closing either direction without that coupling would be a vacuous proof.

**Prerequisites to resume:**

| Step | Deliverable |
|------|-------------|
| P4.1 | Lean (or extracted) `compileClauses : List ActionDSL.ActionClause → DFAM` matching runtime DFA export |
| P4.2 | Semantics builder from the same clauses; trace-level checked predicate folded from per-step `Checked` |
| P4.3 | Soundness + completeness lemmas for that pair; discharge both `sorry`s from those lemmas |

**Policy:** Keep F33 **PARTIAL**. Do not weaken lean-style ENFORCED targets. Do not replace these `sorry`s with `axiom` or `by assumption`.

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
