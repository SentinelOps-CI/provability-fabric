# Policy-trace proof template

Minimal Lean 4 proof template for **"Given this finite trace, every event satisfies Policy P."**

- **PolicyTrace.lean**: Defines `Event` (policy-relevant field: `allowed`), decidable checker `traceSatisfiesPolicy`, and predicate `allEventsSatisfyP`. Theorem `checker_implies_policy` proves that when the checker returns true, every event in the trace satisfies Policy P. No mathlib required for PolicyTrace; the rest of the Spec lib may require mathlib (see lakefile.lean).

## Proof hook (optional --prove)

When running the bench with `--prove`, the runner builds this proof tree (`lake build` in this directory). On success it writes in the run directory:

- **proof.ok** – Sentinel plus `proof_artifact_hash=...`
- **proof_artifact_hash.txt** – SHA256 of the compiled proof artifact

On failure it writes **proof_failure.json** with structured output: `success`, `error`, `message`, `exit_code`, `stdout`, `stderr`.

PF positions Lean proofs as part of spec bundles; this template is the canonical policy-compliance proof hook.
