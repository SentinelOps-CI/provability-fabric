# Evidence acceptance positioning (deliverables 1–5)

Internal reference for acceptance-safe claims. Public counterparts live in specs and roadmap pages; this page consolidates exact wording for deliverables D1–D5.

**Checkpoint:** `main` at `9788bb8a` (2026-06-16). Private acceptance packet: `private/acceptance-evidence/acceptance-2026-06-16/` (gitignored).

## D1 — Schema and specification

> Evidence v0.1/v0.2 JSON schemas, model docs, and the compatibility matrix define a **distinct lane** from PCS science-claim bundles and `so bundle pack` tar archives. Lane separation is enforced by schema IDs, negative tests, and documentation.

**Non-claim:** Schemas do not merge PCS `EvidenceBundle.v0` with Evidence JSON bundles.

## D2 — Bundle tooling

> `pf evidence bundle pack` and `pf evidence validate --strict` provide **digest-bound structural validation** for claim, proof, attestation, and execution-trace artifacts referenced in a bundle manifest.

**Non-claim:** Validation does not verify DSSE/CERT signatures, Lean proof soundness, or PCS admission verdicts.

## D3 — Runtime integration

> The sidecar emits CERT-V1 JSON and appends `evidence_v01_binding` JSONL on the emit path. Cert write paths are guarded by `scripts/check_cert_write_paths.sh`. Runtime binding is verified on **Linux CI** (Evidence smoke) when local Windows `cargo test` is blocked by network/SSL.

**CI authority:** [Evidence smoke run 27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269) — runtime sidecar pytest green.

**Non-claim:** Binding JSONL alone is not bundle validation; not every cert session is auto-packaged into bundles.

## D4 — Replay

> v0.1: static replay checks trace digests and preconditions. v0.2: TRACE-REPLAY-KIT import, `replay_context`, and `pf evidence replay --execute --low-view` for deep deterministic replay when submodules are initialized.

**Non-claim:** `pf check-trace` and `so trace run` are not substitutes for Evidence replay. v0.2 deep replay requires `make submodules`; PR #92 alone does not cover v0.2 execute (cite #99–#101, #105).

## D5 — Verification and closure

> Testbeds, Evidence smoke CI, standards pin checks, and program closure docs (#127–#130) establish the verification gate for the Evidence program. Repo-wide CI inventory remains **not fully green** (8/67 gated workflows on latest inventory); Evidence lane baselines are green.

**Non-claim:** Full-repository CI green is not claimed. Attestation `signature` fields in fixtures are placeholders; CERT-V1 DSSE verification is external (see [attestation signatures](../specs/evidence-attestation-signatures.md)).

## Signature verification decision (2026-06-16)

`pf evidence validate` does **not** include an opt-in `--verify-signatures` hook. Adding one would require algorithm selection, key-trust policy, and CERT-V1 submodule wiring beyond the current structural validator scope.

**Acceptance-safe delegation:**

> Evidence bundles package attestation artifacts and bind them to claim digests. Signature verification is delegated to CERT-V1 tooling and organization-specific verifier policies.

## Suggested release tag (optional)

If tagging after evidence acceptance sign-off: `evidence-v0.2.0-acceptance` or `pcs-pf-v0.1.0-rc3` — follow org release process; tag creation is out of scope for automated closure.

## Related

- [Evidence program closure](../roadmap/evidence-program-closure.md)
- [Evidence v0.2 status](../roadmap/evidence-v0.2-status.md)
- [Evidence attestation signatures](../specs/evidence-attestation-signatures.md)
- [Runtime evidence boundaries](../guides/runtime-evidence-boundaries.md)
