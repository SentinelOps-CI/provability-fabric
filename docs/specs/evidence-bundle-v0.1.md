# Evidence bundle v0.1

## Bundle manifest

An Evidence v0.1 bundle is a single JSON file referencing role-tagged artifacts by path and digest:

```json
{
  "bundle_id": "basic-evidence-bundle",
  "schema_version": "0.1",
  "created_at": "2025-06-01T12:00:00Z",
  "producer": "pf-evidence/v0.1",
  "artifacts": [
    {
      "role": "claim",
      "path": "artifacts/claim.json",
      "media_type": "application/vnd.provability-fabric.evidence.claim+json",
      "digest": "sha256:..."
    }
  ],
  "bundle_digest": "sha256:..."
}
```

## Pack manifest

`pf evidence bundle pack` reads a lighter manifest from the example directory:

```json
{
  "schema_version": "0.1",
  "bundle_id": "basic-evidence-bundle",
  "producer": "pf-evidence/v0.1",
  "artifacts": [
    { "role": "claim", "path": "artifacts/claim.json" }
  ]
}
```

The command resolves paths relative to the manifest directory, computes digests, fills default media types, and writes the bundle JSON.

## Commands

```bash
pf evidence bundle pack --manifest examples/evidence-basic/manifest.json --out /tmp/bundle.json
pf evidence validate /tmp/bundle.json --strict --report-out /tmp/report.json
pf evidence replay --bundle /tmp/bundle.json --out /tmp/replay.json
```

## Canonical hashing

`bundle_digest` covers the bundle object with `bundle_digest` omitted, using UTF-8 JSON and recursively sorted object keys. Implementation: [`core/evidence/bundle.go`](../../core/evidence/bundle.go).

## Validation

Strict mode validates:

1. Bundle JSON Schema
2. `bundle_digest` recomputation
3. Artifact presence and byte digests
4. Role schema validation for claim/proof/attestation/execution-trace artifacts

## Related

- [Evidence model v0.1](evidence-model-v0.1.md)
- [Walkthrough](../guides/evidence-bundle-walkthrough.md)
