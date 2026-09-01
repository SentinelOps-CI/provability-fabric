# Evidence v0.2 schemas

Machine-readable JSON Schema (draft 2020-12) artifacts for the Evidence v0.2 lane. v0.2 is opt-in via `schema_version: "0.2"` and optional `replay_context`; v0.1 bundles remain valid unchanged.

## Layout

| Path | Purpose |
|------|---------|
| `schemas/evidence-bundle.schema.json` | Bundle manifest with `replay_context` and digest-bound artifact refs |
| `schemas/trace-replay-cert.schema.json` | Local fail-closed schema for TRACE-REPLAY-KIT `cert_type: "trace_replay"` outputs |
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
  "fixtures_path": "kit/fixtures",
  "low_view_oracle": true
}
```

## Replay certificate validation boundary

TRACE-REPLAY-KIT emits `cert_type: "trace_replay"` certificates. These are validated fail-closed by Provability Fabric against `schemas/trace-replay-cert.schema.json` after each executed replay and before a low-view result can pass. Acceptance additionally binds each certificate to the exact requested trace metadata and `fixtures/env.json`, requires result event IDs to match the trace event sequence, requires summary counts to agree with the results, and requires every requested event to report `status: "success"`.

Bundle-controlled artifact and replay-context paths are constrained to the declared bundle base directory using both lexical containment and symlink-resolved containment. The replay runner receives the resolved contained trace and fixtures paths, and `fixtures/env.json` is checked separately so a child symlink cannot escape the fixture root.

The trace-replay certificate schema is distinct from `external/CERT-V1/schema/cert-v1.schema.json`, which describes the runtime-sidecar CERT shape. The pinned KIT release may emit a legacy `$schema` URI that is not fetchable; Provability Fabric does not treat that URI as the acceptance authority. The checked-in v0.2 trace-replay schema is the local validation authority for these KIT outputs. The `signature.hash` field is checked only for its declared `sha256` algorithm and digest shape; no stable canonicalization contract is assumed here, so this is not a claim that the self-reported digest or an arbitrary cryptographic signature has been independently authenticated.

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
