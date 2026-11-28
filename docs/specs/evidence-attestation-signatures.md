# Evidence attestation signatures

Evidence bundles may include **attestation** role artifacts that reference signed claims (for example, a proof artifact digest). This document clarifies what `pf evidence validate` guarantees for signatures versus what requires external verification.

## What the attestation artifact carries

The v0.1 attestation schema (`specs/evidence/v0.1/schemas/attestation.schema.json`) requires:

- `attestor` — identifier of the signing party
- `signed_claim_ref` — digest-bound reference to another bundle artifact (role, path, media type, digest)
- `signature` — opaque signature string

Example fixtures use `demo-signature-placeholder` for walkthrough purposes. These are **not** production cryptographic signatures.

## What `pf evidence validate` checks

In `--strict` mode, the Evidence validator:

1. Validates the attestation JSON against `attestation.schema.json`
2. Verifies the attestation artifact digest matches the bundle manifest
3. Checks the individual manifest artifact references and digests.

Plain strict validation does not check the nested `signed_claim_ref` identity.
Use the opt-in reference profile:

```bash
pf evidence validate bundle.json --strict --require-attestation-references
```

This profile requires at least one attestation. It rejects duplicate manifest
paths or attestation IDs, ambiguous JSON keys, noncanonical paths, and a
nested reference that fails to match all four fields (role, path, media
type and digest) of a non-attestation manifest entry. Every manifest entry
must independently pass ordinary strict validation. Validation assumes a
stable bundle snapshot controlled by the verifier. The profile neither
requires coverage of every artifact nor verifies the opaque signature.
Existing illustrative fixtures with stale references must be repaired and
repacked before using this opt-in profile; plain strict validation remains
compatible with them.

Plain strict validation and the reference-only profile do **not**:

- Parse or verify DSSE / COSE / JWT envelope formats
- Validate CERT-V1 `sig` fields on referenced certs
- Invoke cosign, OpenSSL, or CERT-V1 verifier tooling

The execution-attestation profile described below is a separate opt-in signature verification feature with explicit algorithm and key-trust policy.

## Delegated verification (recommended acceptance wording)

> Evidence bundles **package** attestation artifacts and bind them to claim digests. **Signature verification is delegated** to CERT-V1 tooling and organization-specific verifier policies. Demo placeholders in repository fixtures are illustrative only.

### External verifiers

| Artifact type | Verify with |
|---------------|-------------|
| CERT-V1 JSON (`application/vnd.cert-v1+json`) | CERT-V1 schema + DSSE verifier (submodule `external/CERT-V1`) |
| Attestation `signature` over proof/claim | Organization attestor policy; not enforced by `pf evidence validate` |
| PCS signed science-claim bundles | PCS `pf verify` / admission adapters (separate lane) |

## Operational guidance

1. Treat `pf evidence validate --strict` as **structural and digest integrity** for attestations. Use `--require-attestation-references` for explicit nested reference binding. Neither result establishes cryptographic provenance.
2. Run CERT-V1 verification on any packaged cert artifacts before trusting enforcement claims.
3. Replace fixture placeholders with real signatures only in deployment-specific bundles; do not commit production keys to the public repository.

## Related

- [Runtime evidence boundaries](../guides/runtime-evidence-boundaries.md)
- [Evidence compatibility matrix](evidence-compatibility.md)
- [Replay guarantees](../guides/replay-guarantees.md)


## Independently selected execution attestation profile

The opt-in `--execution-attestation-trust PATH --strict` profile additionally
verifies every attestation signature over the single expected execution trace.
The verifier supplies a trusted JSON file independently of the bundle:
```json
{
  "profile": "ed25519-execution-v1",
  "expected_bundle_id": "deployment-selected-run",
  "expected_trace_digest": "sha256:<64 lowercase hexadecimal characters>",
  "attestor": "deployment-selected-attestor",
  "public_key_base64": "<canonical standard base64 of 32 raw Ed25519 public key bytes>"
}
```
The trace digest refers to raw artifact bytes, not the internal trace_digest
field. All attestations must reference exactly that trace and selected attestor.
The signature field uses `ed25519-execution-v1:` followed by canonical standard
base64 of the 64-byte signature. The signed preimage is the ASCII domain
`provability-fabric/execution-attestation/v1` followed by NUL, then ten UTF-8
strings, each preceded by its unsigned 64-bit big-endian byte length:
bundle schema version, bundle ID, attestation schema version, attestation ID,
attestor, target role, target path, target media type, target digest and
attestation's optional media_type (empty if absent). Signature bytes and
outer bundle digest are excluded to avoid circular commitments.

The profile establishes that the selected key signed a reference to the
externally selected trace in the specified bundle identity. It does not
authenticate the real-world execution, establish completeness of mediation,
check internal trace semantics, attest other artifacts, certify replay,
or implement freshness, key distribution or revocation. The verifier must
control the trust policy, key selection, expected run identity and stable
bundle snapshot. The CLI never derives trust roots from bundle contents.
