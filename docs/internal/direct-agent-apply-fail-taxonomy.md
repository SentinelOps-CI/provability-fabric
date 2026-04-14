# Direct Agent Apply-Fail Taxonomy (Strict 10 Tuned)

Source run: `runs/direct-agent-ab-gate-10-tuned`

## Summary

Strict compare failed with `patch_apply.applies_false=5`. All five failures were `empty patch` outcomes (not malformed diff syntax).

## Instance Classification

| Instance ID | Run | Failure Type | Evidence | Fix Rule |
|---|---|---|---|---|
| `pytest-dev__pytest-11143` | baseline `20260323-160630-0d322425` | `empty_patch` | `patch_apply_check.json` -> `stderr: "empty patch"` | Enforce patch-quality loop: if empty patch, run one constrained repair iteration before finalizing. |
| `pylint-dev__pylint-5859` | baseline `20260323-160630-0d322425` | `empty_patch` | `patch_apply_check.json` -> `stderr: "empty patch"` | Same: deterministic non-empty patch gating and typed failure. |
| `pytest-dev__pytest-11143` | candidate `20260323-162950-c0ee006a` | `empty_patch` | `patch_apply_check.json` -> `stderr: "empty patch"` | Same: patch-quality loop + no quality-based fallback masking. |
| `mwaskom__seaborn-2848` | candidate `20260323-162950-c0ee006a` | `empty_patch` | `patch_apply_check.json` -> `stderr: "empty patch"` | Same: constrained repair attempt and fail typed if still empty. |
| `matplotlib__matplotlib-18869` | candidate `20260323-162950-c0ee006a` | `empty_patch` | `patch_apply_check.json` -> `stderr: "empty patch"` | Same: constrained repair attempt and fail typed if still empty. |

## Deterministic Rules Adopted

1. Patch sanitation runs on every candidate patch.
2. Local `git apply --check` runs before returning a patch.
3. If patch is empty or fails apply-check, execute one constrained repair iteration (not full re-solve).
4. Persist typed patch failure class in trace (for audit and gating).
