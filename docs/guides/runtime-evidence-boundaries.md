# Runtime evidence boundaries

## Runtime evidence overview

Runtime evidence in Evidence v0.1 is an **additive binding layer** on top of existing CERT-V1 sidecar emission. The sidecar continues to write CERT-V1 JSON and append CERT lines to `evidence/logs/sidecar.jsonl`. When `EVIDENCE_BUNDLE_REF` is set, emit paths also append an `evidence_v01_binding` JSONL event linking the session, cert path, optional bundle reference, and cert digest.

## Event sources

| Source | Event | Output |
|--------|-------|--------|
| Sidecar `emit` handling | `permit_enforcement` CERT emission | `evidence/certs/<session>/<seq>.cert.json` |
| Binding hook | `write_cert_with_binding` | `evidence/logs/sidecar.jsonl` (`evidence_v01_binding`) |
| Platform services | evidence-service, replay-service | Out of v0.1 bundle scope unless explicitly packaged |

## Artifact binding

Binding events record:

- `session_id`, `cert_path`
- Optional `evidence_bundle_ref` (from `EVIDENCE_BUNDLE_REF`)
- `artifact_digests.cert-v1` (SHA-256 of the written CERT file)

CERT-V1 itself is **not modified**. Full v0.1 bundles are assembled separately via `pf evidence bundle pack`.

## Trust assumptions

- Sidecar process integrity and filesystem write permissions
- CERT-V1 schema validation at write time (external schema required)
- Digest computation over bytes actually written to disk
- Bundle references are opaque paths unless validated by `pf evidence validate --strict`

## Enforcement boundary

Runtime binding records **what the sidecar emitted** and **optional cross-links** to bundle manifests. It does **not**:

- Prove policy correctness
- Prove proof soundness
- Aggregate multi-session evidence automatically
- Replace PCS admission or SWE-bench evidence writers

## What is recorded

- CERT-V1 payloads (existing behavior)
- Optional `evidence_v01_binding` JSONL with schema version `0.1`
- Cert file digest under role `cert-v1`

## What is not recorded

- Full claim/proof/trace artifacts (unless packaged into bundles separately)
- TRACE-REPLAY-KIT execution output (unless referenced in a bundle)
- Cross-tenant bundle aggregation
- DSSE signature verification state beyond CERT `sig` field presence

## What validation proves

`pf evidence validate --strict` on a v0.1 bundle proves:

- Schema conformance for the bundle manifest
- Referenced artifact presence and byte digests
- Self-consistent `bundle_digest`

Binding JSONL alone is **not** validated by the bundle validator unless included as bundle artifacts.

## What validation does not prove

- Runtime binding events were emitted for every cert
- CERT signatures are valid DSSE envelopes
- Replay determinism of external systems
- Science-claim admission (PCS domain)

## Failure modes

- Invalid CERT: deny-wins via existing `validate_cert` (cert not written)
- Binding write failure after cert write: cert remains; binding may be absent
- Missing `external/CERT-V1` schema: sidecar panics at schema load (existing behavior)

## Tamper semantics

Tampering CERT bytes after write invalidates `artifact_digests.cert-v1` in a subsequent binding event only if rebinding occurs. Bundle-level tamper detection requires `pf evidence validate --strict` on the packaged bundle.

## Replay relationship

Runtime binding does not execute replay. Bundles that include `execution-trace` artifacts may be checked with `pf evidence replay`. See [Replay guarantees](replay-guarantees.md).

## Operational guidance

1. Clone `external/CERT-V1` before running sidecar in strict environments.
2. Set `EVIDENCE_BUNDLE_REF` when linking emissions to a known bundle manifest path.
3. Package certs and traces into v0.1 bundles with `pf evidence bundle pack`.
4. Validate bundles before archival: `pf evidence validate <bundle> --strict`.

## Related

- [Runtime evidence basic](runtime-evidence-basic.md)
- [Compatibility matrix](../specs/evidence-compatibility.md)
- [Evidence model v0.1](../specs/evidence-model-v0.1.md)
