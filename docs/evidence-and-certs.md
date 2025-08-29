## Evidence & CERTs

The sidecar emits a CERT-V1 JSON for each relevant emission (emit events and session end) and appends a JSONL line to `evidence/logs/sidecar.jsonl`.

- Schema: `external/CERT-V1/schema/cert-v1.schema.json`
- Output path: `evidence/certs/<session>/<seq>.cert.json`

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

The `ni_monitor` field records the local \MonNI verdict for the relevant prefix. The global NI claim remains bound to the proof hash and is verified externally.

See also: `docs/standards.md` and the CERT-V1 repository.


