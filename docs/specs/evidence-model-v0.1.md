# Evidence model v0.1

## Overview

Evidence v0.1 defines a narrow JSON artifact lane for packaging verifiable claims, proofs, attestations, and execution traces with digest-bound references. It complements existing CERT-V1 emission and TRACE-REPLAY-KIT tooling without replacing them.

## Goals

- Stable JSON Schema artifacts with `schema_version: "0.1"`
- Digest-bound artifact references (`sha256:<hex>`)
- Strict validation and tamper detection
- CLI commands under `pf evidence`
- Documented compatibility with runtime and replay surfaces

## Non-goals

- PCS science-claim bundles (`EvidenceBundle.v0`)
- Spec bundle tar archives (`so bundle pack`)
- Redefining CERT-V1 (external compatible type only)

## Artifact types

| Type | Schema | Purpose |
|------|--------|---------|
| Claim | `claim.schema.json` | Declarative behavioral statement |
| Proof | `proof.schema.json` | Proof artifact with refs + `proof_digest` |
| Attestation | `attestation.schema.json` | Signed claim ref (CERT-V1 compatible role) |
| Execution trace | `execution-trace.schema.json` | Ordered events + `trace_digest` |
| Evidence bundle | `evidence-bundle.schema.json` | Manifest composing artifact refs |
| Validation report | `validation-report.schema.json` | Strict validation outcome |

## Evidence bundle structure

A bundle is a single JSON document with `bundle_id`, `schema_version`, `artifacts[]`, `bundle_digest`, `created_at`, and `producer`. Each artifact entry includes `role`, `path`, `media_type`, and `digest`. See [Bundle format](evidence-bundle-v0.1.md).

## Claims

Claims (`claim_id`, `statement`, `subject`) describe what is being asserted. Claims are referenced by proofs and attestations but do not embed proof material.

## Proof artifacts

Proofs bind a `proof_system` identifier to `artifact_refs` and a canonical `proof_digest`. Proofs may reference claims and other artifacts by digest.

## Attestations

Attestations wrap a `signed_claim_ref` and `signature`. CERT-V1 JSON may be referenced using media type `application/vnd.cert-v1+json` without redefining the external schema.

## Execution traces

Traces contain ordered `events` with `seq` and `kind`, plus a self-referential `trace_digest`. TRACE-REPLAY-KIT output may be adapted into this shape.

## Validation reports

Reports capture `status` (`pass`|`fail`), `errors`, `warnings`, `bundle_ref`, and `validated_at`. Emitted by `pf evidence validate --strict`.

## Digest rules

- File artifacts: SHA-256 over raw bytes (`sha256:<hex>`)
- Self-referential digests (`proof_digest`, `trace_digest`, `bundle_digest`): canonical JSON with sorted object keys, excluding the digest field itself
- Bundle manifest hashing uses the same canonicalization as [`core/evidence/digest.go`](../../core/evidence/digest.go)

## CERT compatibility

CERT-V1 JSON MAY appear as an attestation-compatible artifact using media type `application/vnd.cert-v1+json`. The external schema remains authoritative.

## Replay compatibility

Execution traces produced by TRACE-REPLAY-KIT or SWE-bench metadata MAY be referenced as `execution-trace` role artifacts. `pf evidence replay` verifies bundle integrity and trace self-digest; it does not replace `so trace run`.

## Failure and tamper semantics

Strict validation fails closed on:

- Missing schema files
- JSON Schema violations
- Missing referenced artifact files
- Digest mismatches
- Invalid self-referential digests

## Versioning

Only `0.1` is defined in this release. Future versions require new schema paths and compatibility documentation.

## Limitations

See [Evidence v0.1 roadmap](../roadmap/evidence-v0.1.md) for platform caveats (`check-trace`, cert validator fail-open history, Windows test gaps).

## Related

- [Bundle format](evidence-bundle-v0.1.md)
- [Compatibility matrix](evidence-compatibility.md)
- [Schemas](../../specs/evidence/v0.1/README.md)
