# Evidence v0.2 schemas

Machine-readable JSON Schema (draft 2020-12) artifacts for the Evidence v0.2 lane. v0.2 is opt-in via `schema_version: "0.2"` and optional `replay_context`; v0.1 bundles remain valid unchanged.

## Layout

| Path | Purpose |
|------|---------|
| `schemas/evidence-bundle.schema.json` | Bundle manifest with `replay_context` and digest-bound artifact refs |
| `examples/valid/manifest.json` | Valid v0.2 bundle fixture |
| `examples/valid/deep-replay-bundle.json` | Fixture with KIT trace paths for deep replay |
| `examples/valid/artifacts/` | Claim, proof, attestation, execution-trace samples |
| `examples/valid/kit/` | TRACE-REPLAY-KIT trace and env fixtures |
| `examples/valid/replay-out/` | Expected replay CERT outputs |

## Stable `$id`

Each schema exposes a stable HTTPS `$id` under:

`https://provability-fabric.org/schemas/evidence/v0.2/<name>.schema.json`

## Required fields

Top-level bundles require `schema_version: "0.2"`, `bundle_id`, `artifacts`, `bundle_digest`, `created_at`, and `producer`. Artifact references use the same digest-bound shape as v0.1:

```json
{ "role": "...", "path": "...", "media_type": "...", "digest": "sha256:<hex>" }
```

Optional `replay_context` enables deep replay (`pf evidence replay --execute [--low-view]`):

```json
{
  "kit_trace_path": "kit/trace.json",
  "fixtures_path": "kit/fixtures/env.json",
  "low_view_oracle": true
}
```

## Tests and verification

| Gate | Command |
|------|---------|
| Go pack/validate | `cd core/evidence && go test ./...` |
| CLI strict validate | `pf evidence validate --strict <bundle>` |
| Deep replay testbed | `testbed/evidence-v0.2/run_deep_replay.sh --execute` |
| CI smoke | `.github/workflows/evidence-v01-smoke.yml` (covers v0.1 + v0.2) |

## Related docs

- [Evidence model v0.1](../../../docs/specs/evidence-model-v0.1.md) â€” shared artifact roles
- [Evidence v0.2 integration](../../../docs/roadmap/evidence-v0.2.md) â€” definition of done
- [Evidence v0.2 status](../../../docs/roadmap/evidence-v0.2-status.md) â€” delivery tracker
- [Compatibility matrix](../../../docs/specs/evidence-compatibility.md) â€” v0.1 vs v0.2 vs PCS
- [Evidence v0.1 schemas](../v0.1/README.md) â€” prior schema lane
