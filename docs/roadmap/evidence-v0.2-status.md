# Evidence v0.2 status (redirect)

> **Archived.** The full historical tracker is at [archive/evidence-v0.2-status.md](../internal/archive/evidence-v0.2-status.md).

**Live CI posture:** [evidence-program-closure.md](evidence-program-closure.md) and [remediation-tracker.md](../internal/remediation-tracker.md).

### Explicit non-claims

Guarantees are conditional on configured trust roots and deployment policy. In particular:

- Lean proofs in-repo do **not** mean every production path is proven end-to-end.
- Evidence validate is structural and digest-bound; it does **not** perform semantic Lean checking inside the Evidence lane.
- In-validator CERT-V1 / attestation signature verification (`--verify-signatures`) remains out of scope unless a deployment adds an external verifier.
- DSSE verification is fail-closed by default when enforcing (`PF_ENFORCE_DSSE` unset or truthy); opt out only with `PF_ENFORCE_DSSE=0` / `false`, and a trust root is required when enforcing.

See also [architecture/guarantees.md](../architecture/guarantees.md) and [deployment trust](../guides/deployment-guide.md#production-trust-chain-environment-f01--f02).
