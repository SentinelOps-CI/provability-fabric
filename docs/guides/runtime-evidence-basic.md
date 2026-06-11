# Runtime evidence basic

Sidecar-watcher emits CERT-V1 certificates and may append additive Evidence v0.1 binding records.

## Binding event

`write_cert_with_binding` writes the CERT as today, then appends a JSONL line shaped like:

```json
{
  "event_type": "evidence_v01_binding",
  "session_id": "runtime-demo-001",
  "cert_path": "evidence/certs/runtime-demo-001/1.cert.json",
  "evidence_bundle_ref": "examples/runtime-evidence-basic/basic-evidence-bundle.json",
  "artifact_digests": { "cert-v1": "sha256:..." },
  "schema_version": "0.1"
}
```

Implementation: [`runtime/sidecar-watcher/src/evidence_v01.rs`](../../runtime/sidecar-watcher/src/evidence_v01.rs).

## Example bundle

`examples/runtime-evidence-basic/basic-evidence-bundle.json` validates with:

```bash
pf evidence validate examples/runtime-evidence-basic/basic-evidence-bundle.json --strict
```

## Related

- [Runtime evidence boundaries](runtime-evidence-boundaries.md)
- [Evidence overview](../evidence/overview.md)
