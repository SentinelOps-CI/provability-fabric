# Computation reproducibility release fixtures

Release fixtures for workflow `scientific_computation.reproducibility_v0` document computation witnesses and release-chain validation for the reproducibility profile.

The workflow profile appears in `examples/workflow_profiles/scientific_computation_reproducibility.valid.json`, and the guide is [docs/workflow-profiles.md](../../docs/workflow-profiles.md).

## Artifacts

| File | Type |
|------|------|
| `dataset_receipt.json` | `DatasetReceipt.v0` |
| `environment_receipt.json` | `EnvironmentReceipt.v0` |
| `computation_run_receipt.json` | `ComputationRunReceipt.v0` |
| `result_artifact.json` | `ResultArtifact.v0` |
| `computation_witness.json` | `ComputationWitness.v0` |
| `science_claim_bundle.certified.json` | `ScienceClaimBundle.v0` |
| `verification_result.json` | `VerificationResult.v0` |
| `signed_science_claim_bundle.json` | `SignedScienceClaimBundle.v0` |
| `release_manifest.v0.json` | `ReleaseManifest.v0` |
| `release_chain_validation_result.v0.json` | `ReleaseChainValidationResult.v0` |

## Validate

```bash
pcs validate-release-chain examples/computation-release/
pcs conformance run --suite computation
```

Regenerate through the Python materialize script.

```bash
cd python
python scripts/materialize_computation_fixtures.py
```

Invalid cases live under `examples/computation-release-invalid/` with one failure class per directory.
