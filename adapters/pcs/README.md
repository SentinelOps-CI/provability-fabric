# PCS adapter

Verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts.

## Documentation

User guides live under [docs/pcs/](../../docs/pcs/README.md).

- [Quickstart](../../docs/pcs/quickstart.md)
- [Verification](../../docs/pcs/verification.md)
- [Admission benchmarks](../../docs/pcs/admission-benchmarks.md)
- [Fixtures](../../docs/pcs/fixtures.md)

## Responsibilities

- Load LabTrust-certified science claim bundles (`runtime_receipts[]`, `certificates[]`, `schema_version` `"v0"`)
- Reject legacy singular-field bundle shapes
- Run 17 consistency, provenance, registry, and status-transition checks
- Enforce release-mode admission (handoff manifest, artifact registry, admission profile)
- Apply admission profiles in `admission_profiles/` (`labtrust_qc_release`, `agent_tool_use_safety`, `scientific_computation_reproducibility`)
- Emit `ReleaseChainValidationResult.v0` and `VerificationResult.v0`
- Build `SignedScienceClaimBundle.v0` for Scientific Memory import

## Quick commands

```bash
make demo-pcs
make test-pcs
```

Release-mode verify:

```bash
./pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --admission-profile labtrust_qc_release \
  --release-mode
```

## Package layout

| File | Role |
|------|------|
| `bundle_validator.go` | 17-check verification pipeline |
| `artifact_registry.go` | ArtifactRegistry.v0 loader |
| `handoff_manifest.go` | HandoffManifest.v0 + legacy handoff detection |
| `release_chain_validation.go` | ReleaseChainValidationResult.v0 emission |
| `release_manifest.go` | ReleaseManifest.v0 loader |
| `admission_profile.go` | Admission profiles and release-mode resolution |
| `tool_use_admission.go` | Tool-use admission rules |
| `release_mode.go` | Release-mode policy |
| `registry_semantic_audit.go` | Registry semantic check execution |
| `registry_validate.go` | Registry bundle and manifest admission |
| `registry_release_chain.go` | Registry release-chain checks |
| `explain.go` | Failure explanations |
| `canonical_hash.go` | pcs-core canonical JSON digest |
| `status_transition.go` | Status transition policy |
| `array_checks.go` | Runtime receipt and certificate cardinality |
| `schema_validate.go` | JSON Schema validation |
| `signed_bundle.go` | Sign and inspect integrity |
| `legacy.go` | Legacy detection and migration |
| `paths.go` | Repo-root path resolution |
| `schemas/*.json` | Embedded pcs-core schema mirror |

## Tests

```bash
cd adapters/pcs && go test ./... -count=1
```

Set `PCS_CORE_PATH` for schema mirror and benchmark validation tests.

Canonical artifact vocabulary lives in [pcs-core](https://github.com/SentinelOps-CI/pcs-core).
