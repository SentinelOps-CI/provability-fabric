# Runtime evidence basic

Demonstrates additive Evidence v0.1 binding alongside CERT-V1 sidecar emission.

## Static path (always)

Checked-in fixtures — no live sidecar required:

- `binding-event.json` — JSONL-shaped binding record emitted by `write_cert_with_binding`
- `basic-evidence-bundle.json` — bundle referencing runtime artifacts

```bash
bash examples/runtime-evidence-basic/run_scenario.sh
```

## Live path (optional)

When `external/CERT-V1` is cloned (`make submodules`), exercise the permit-enforcement emit path:

```bash
bash examples/runtime-evidence-basic/run_scenario.sh --live
```

CI runs the live path via `tests/runtime_evidence/test_runtime_evidence_sidecar.py` on Linux when the CERT-V1 schema is present.

See [Runtime evidence basic](../../docs/guides/runtime-evidence-basic.md) and the PR8 sidecar integration test.
