# Runtime evidence basic

Sidecar-watcher emits CERT-V1 certificates and **always** appends Evidence v0.1 binding records on the permit-enforcement emit path.

## Emit path (v0.2 scope)

Binding events are written from the **permit enforcement** emit path only (`permit_enforcement.rs` → `write_cert_with_binding`). This is the single production CERT write hook in `runtime/` (enforced by `scripts/check_cert_write_paths.sh` in CI). Other sidecar code paths do not emit CERT files in production.

`evidence_bundle_ref` in the binding event is **optional** and populated only when `EVIDENCE_BUNDLE_REF` is set. The binding JSONL line is emitted regardless.

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

Run the static or live scenario:

```bash
bash examples/runtime-evidence-basic/run_scenario.sh
bash examples/runtime-evidence-basic/run_scenario.sh --live   # cargo test emit + binding (requires make submodules)
```

## CI requirements (live test)

- Linux runner (`ubuntu-latest`)
- `external/CERT-V1` submodule present (`make submodules`)
- `tests/runtime_evidence/test_runtime_evidence_sidecar.py` gates on both; skipped on Windows local runs

## Related

- [Runtime evidence boundaries](runtime-evidence-boundaries.md)
- [Evidence overview](../evidence/overview.md)
