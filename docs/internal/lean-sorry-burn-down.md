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

## Out-of-scope sorry inventory (2026-07-03)

| File | `sorry` count | Priority | Rationale |
|------|--------------:|----------|-----------|
| `core/lean-libs/Invariants.lean` | **0** | **P1** | **DONE** — sorry-free; **CI-enforced** as of 2026-07-03 (Wave 7 F33) |
| `proofs/Policy.lean` | **0** | **P2** | **DONE** — `soundness`, `completeness`, `read_requires_label_flow` (role-gated), `ni_bridge` (with label-coherence hypothesis) proved 2026-07-03 |
| `Policy.lean` (repo root) | 4 | **P3** | Parallel copy; consolidate with `proofs/Policy.lean` |
| `core/lean-libs/Runtime/MicroInterp.lean` | 2 | **P4** | Runtime micro-interpreter; not in enforced set |

**Total outside enforced set:** 6 occurrences (was 24; **18 eliminated** in Invariants.lean + proofs/Policy.lean F33 burn-down through 2026-07-03).

## Burn-down sequence

1. **Align canonical Policy** — pick `proofs/Policy.lean` as source of truth; root `Policy.lean` becomes thin re-export or is deleted after migration.
2. **Invariants.lean (DONE)** — proved 2026-07-02–03: `empty_trace_invariant`, `privacy_budget_additive`, `system_safety`, `plan_validation_preserves_invariants`, `label_flow_preservation`, egress cert namespace (`generateCertificate`, `certificate_integrity`, `policy_hash_verification`, `transitive_non_interference`, `label_flow_monotonicity`, etc.).
3. **proofs/Policy.lean (DONE)** — proved 2026-07-03: `soundness`, `completeness`, role-gated `read_requires_label_flow`, `ni_bridge` with explicit prefix label-coherence hypothesis.
4. **MicroInterp.lean (2 sorry)** — lower priority; runtime semantics, not gating CI.
5. **Expand enforced set** — **Invariants.lean added** to `lean-style.yaml` ENFORCED list (2026-07-03); root `Policy.lean` consolidation remains.

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
