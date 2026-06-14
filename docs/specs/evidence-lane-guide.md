# Evidence lane guide

Three bundle lanes coexist in Provability-Fabric. They are intentionally **not** merged in Evidence v0.2.

## Lane 1 — Evidence v0.1 / v0.2 (`pf evidence`)

- JSON manifest with digest-bound `artifacts[]` roles (`claim`, `proof`, `attestation`, `execution-trace`, …).
- Optional v0.2 `replay_context` for executable KIT replay.
- CLI: `pf evidence bundle pack`, `validate --strict`, `trace import`, `replay [--execute]`.

## Lane 2 — PCS `EvidenceBundle.v0`

- Science-claim admission, signed bundles, registry checks.
- Schema: `config/schemas/pcs/EvidenceBundle.v0.schema.json`.
- CLI: `pf verify science-claim`, PCS adapter tests.

## Lane 3 — Spec tar archives (`pf bundle pack` / `so bundle pack`)

- Deployment-oriented tar.gz archives of policy/spec files.
- Not validated by Evidence JSON schemas.

## Decision checklist

1. If you need digest-bound runtime artifacts and replay reports → **Evidence lane**.
2. If you need PCS release admission → **PCS lane** (see [PCS quickstart](../pcs/quickstart.md)).
3. If you need to ship spec files as an archive → **Spec tar lane**.

Never run `pf evidence validate` on PCS or tar artifacts expecting cross-lane compatibility.
