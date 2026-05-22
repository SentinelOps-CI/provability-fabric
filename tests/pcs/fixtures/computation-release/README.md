# Scientific computation reproducibility release train

Conformance fixture for workflow `scientific_computation.reproducibility_v0`.

## Artifacts

Runtime receipts include `dataset_receipt.json`, `environment_receipt.json`, `computation_run_receipt.json`, and `result_artifact.json`. The certificate artifact is `computation_witness.json`. The PCS chain includes `science_claim_bundle.certified.json`, `verification_result.json`, `signed_science_claim_bundle.json`, `release_manifest.v0.json`, and `release_chain_validation_result.v0.json`.

Regenerate with the materialize script and validate the release chain.

```bash
cd python
python scripts/materialize_computation_fixtures.py
pcs validate-release-chain ../examples/computation-release/
```

Invalid negative cases appear under `examples/computation-release-invalid/` with one failure class per directory.
