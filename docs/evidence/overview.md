# Evidence and CERTs

This document describes where evidence and CERTs live, how they are produced, and how to validate them.

## Where evidence and CERTs live

- **Sidecar/runtime**: CERT-V1 files under `evidence/certs/<session>/<seq>.cert.json`. The sidecar emits a CERT-V1 JSON for each relevant emission (emit events and session end) and appends a JSONL line to `evidence/logs/sidecar.jsonl`.
- **Replay (TRACE-REPLAY-KIT)**: CERTs under `tests/replay/out/certs/`.
- **SWE-bench runs**: Under `runs/<run_id>/<instance_id>/`: `run.log`, `model.patch`, `metadata.json` (with `engine_mode`, `engine_success`, `engine_error`, and optional `workspace_manifest_sha256`, `policy_name`, `policy_hash`), `patch_apply_check.json` (applies, stderr, base_commit, resolved_commit, git_version), `engine_trace.json`, `workspace_manifest.json` (when workspace used), `replay_bundle.json` (when capture runs), `cost_report.json`. When guarded: `evidence/` and `policy_compliance_summary.json` are written unconditionally (even when the engine raises or fails); `evidence/events.jsonl` (hash-chained) includes at least a `run_started` event per instance. At run level when `--prove` succeeds: `proof.ok`, `proof_artifact_hash.txt`; on failure: `proof_failure.json`. Aggregate cost: `runs/<run_id>/summary.json` and `summary.csv`. PF metadata sidecar: `predictions.pfmeta.jsonl` (same path stem as `predictions.jsonl`) links instance_id to run_id, policy_hash, trace_hash, replay_bundle_hash, proof_artifact_hash, cost_metrics.

## Schema and output paths

- **Schema**: `external/CERT-V1/schema/cert-v1.schema.json`
- **Output path**: `evidence/certs/<session>/<seq>.cert.json`

Example (abbreviated):

```json
{
  "bundle_id": "sha256:...",
  "policy_hash": "sha256:...",
  "proof_hash": "sha256:...",
  "automata_hash": "sha256:...",
  "labeler_hash": "sha256:...",
  "ni_monitor": "accept",
  "permit_decision": "accept",
  "path_witness_ok": true,
  "label_derivation_ok": true,
  "epoch": 12,
  "sidecar_build": "1.3.2+2025-08-01",
  "egress_profile": "EGRESS-DET-P1@1.0",
  "morph": {
    "env_snapshot_digest": "sha256:...",
    "branch_id": "pf-branch-00023",
    "base_image": "sentinelops/sidecar:1.3.2"
  },
  "sig": "dsse:..."
}
```

The `ni_monitor` field records the local MonNI verdict for the relevant prefix. The global NI claim remains bound to the proof hash and is verified externally.

## Validating CERTs

Validate CERTs (CI and local):

```bash
make validate-certs
```

This runs `tools/cert-validate/validate.py` against the schema at `external/CERT-V1/schema/cert-v1.schema.json`.

## Reading CERT fields (high level)

- `bundle_id`, `policy_hash`, `proof_hash`, `automata_hash`, `labeler_hash`: cryptographic anchors to the bundle, policy, and proofs
- `ni_monitor`: local MonNI prefix verdict (inapplicable|accept|reject|error)
- `permit_decision`: permitD outcome (accept|reject|error)
- `path_witness_ok`, `label_derivation_ok`: IFC witness checks
- `epoch`, `sidecar_build`, `egress_profile`: runtime context
- optional `morph`: environment snapshot info when running on Morph
- `sig`: signature for the CERT payload

See also: [Standards](../specs/standards.md), [Replay](replay.md), the CERT-V1 repository for the full schema, and the [Evidence v0.1 roadmap](../roadmap/evidence-v0.1.md) for the planned bundle format and surface map.

## Evidence surface map

Today the repository exposes several evidence-related paths. Evidence v0.1 (in progress) adds a
JSON bundle lane without replacing these surfaces.

| Surface | Location | Role |
|---------|----------|------|
| Runtime CERT-V1 | `evidence/certs/<session>/<seq>.cert.json` | Sidecar-emitted certificates |
| Sidecar log | `evidence/logs/sidecar.jsonl` | Hash-chained JSONL events |
| TRACE-REPLAY-KIT | `tests/replay/out/certs/` (and trace outputs) | Replay-oriented CERTs and traces |
| SWE-bench runs | `runs/<run_id>/<instance_id>/` | Run logs, metadata, replay bundles |
| PCS science claims | `config/schemas/pcs/EvidenceBundle.v0.schema.json` | Distinct domain; not v0.1 bundles |
| Spec archives | `so bundle pack` | tar.gz spec bundles; out of v0.1 scope |

Planned v0.1 additions (`specs/evidence/v0.1/`, `pf evidence …`) are tracked in the
[Evidence v0.1 roadmap](../roadmap/evidence-v0.1.md).
