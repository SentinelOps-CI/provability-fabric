## Evidence

Where CERTs live:
- Sidecar/runtime writes CERT-V1 files under `evidence/certs/<session>/<seq>.cert.json`.
- Replay runs write CERTs under `tests/replay/out/certs/`.

Validate CERTs (CI and local):
```
make validate-certs
```
This runs `tools/cert-validate/validate.py` against the schema at `external/CERT-V1/schema/cert-v1.schema.json`.

Reading CERT fields (high level):
- `bundle_id`, `policy_hash`, `proof_hash`, `automata_hash`, `labeler_hash`: cryptographic anchors to the bundle, policy, and proofs
- `ni_monitor`: local MonNI prefix verdict (inapplicable|accept|reject|error)
- `permit_decision`: permitD outcome (accept|reject|error)
- `path_witness_ok`, `label_derivation_ok`: IFC witness checks
- `epoch`, `sidecar_build`, `egress_profile`: runtime context
- optional `morph`: environment snapshot info when running on Morph
- `sig`: signature for the CERT payload

See also: `docs/standards.md`, `docs/Replay.md`, and the CERT-V1 repository for the full schema.


