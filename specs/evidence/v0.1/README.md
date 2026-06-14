# Evidence v0.1 schemas

Machine-readable JSON Schema (draft 2020-12) artifacts for the Evidence v0.1 lane.

## Layout

| Schema | Purpose |
|--------|---------|
| `claim.schema.json` | Declarative claim about agent behavior |
| `proof.schema.json` | Proof artifact with digest-bound refs |
| `attestation.schema.json` | Attestation over a signed claim ref |
| `execution-trace.schema.json` | Ordered execution trace with self-digest |
| `evidence-bundle.schema.json` | Bundle manifest composing artifact refs |
| `validation-report.schema.json` | Strict validation outcome report |

## Stable `$id`

Each schema exposes a stable HTTPS `$id` under:

`https://provability-fabric.org/schemas/evidence/v0.1/<name>.schema.json`

## Required fields

All top-level artifacts include `schema_version: "0.1"`. Artifact references use:

```json
{ "role": "...", "path": "...", "media_type": "...", "digest": "sha256:<hex>" }
```

## Tests

Bundle pack and digest coverage lives in Go (`core/evidence/bundle_test.go`, run `go test ./...` in that module). `tests/evidence_bundle/test_bundle_pack.py` is a thin pytest shim so pack tests appear in the Evidence test suite without duplicating Go logic.

## Related docs

- [Evidence model v0.1](../../docs/specs/evidence-model-v0.1.md)
- [Evidence bundle v0.1](../../docs/specs/evidence-bundle-v0.1.md)
- [Compatibility matrix](../../docs/specs/evidence-compatibility.md)
