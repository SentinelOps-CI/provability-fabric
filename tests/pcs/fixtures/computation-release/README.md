# Scientific computation reproducibility release train

Conformance fixture for workflow `scientific_computation.reproducibility_v0`.

## Artifacts

- Runtime: `dataset_receipt.json`, `environment_receipt.json`, `computation_run_receipt.json`, `result_artifact.json`
- Certificate: `computation_witness.json`
- PCS chain: `science_claim_bundle.certified.json`, `verification_result.json`, `signed_science_claim_bundle.json`, `release_manifest.v0.json`, `release_chain_validation_result.v0.json`

Regenerate:

```bash
cd python
python scripts/materialize_computation_fixtures.py
pcs validate-release-chain ../examples/computation-release/
```

Invalid negative cases: `examples/computation-release-invalid/` (one failure class per directory).
