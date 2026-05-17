# PCS adapter (Provability Fabric)

Verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts for the Proof-Carrying Lab Workflow v0.1.

## Responsibilities

- Load LabTrust-certified science claim bundles (`runtime_receipts[]`, `certificates[]`, `schema_version: "v0"`)
- Reject legacy singular-field PF bundles at load and schema validation
- Run 17 consistency, provenance, registry, and status-transition checks
- Consume `HandoffManifest.v0` and emit `ReleaseChainValidationResult.v0`
- Verify bundle admission against `ReleaseManifest.v0` (artifact registry until `ArtifactRegistry.v0` ships)
- Emit `VerificationResult.v0` with `ProofChecked` / `Rejected` status
- Build `SignedScienceClaimBundle.v0` wrappers for Scientific Memory import

## Usage (via CLI)

```bash
./pf verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
./pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json --release-mode
./pf verify release-chain --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --artifact-dir ../pcs-core/examples/labtrust-release --out /tmp/release_chain_validation_result.json
./pf sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json --out /tmp/signed.json
./pf inspect science-claim /tmp/signed.json --strict
./pf inspect science-claim tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json --reverify
./pf migrate science-claim tests/pcs/invalid_legacy_singular_runtime_receipt.json --out /tmp/migrated.json
./pf validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
./pf validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
./pf validate release-chain-result tests/pcs/fixtures/labtrust-release/release_chain_validation_result.json
```

Canonical artifact vocabulary: [pcs-core](https://github.com/SentinelOps-CI/pcs-core).

## Package layout

| File | Role |
|------|------|
| `bundle_validator.go` | 17-check verification pipeline |
| `handoff_manifest.go` | HandoffManifest.v0 + legacy `pf_handoff.json` |
| `release_chain_validation.go` | ReleaseChainValidationResult.v0 emission |
| `release_manifest.go` | ReleaseManifest.v0 / artifact registry loader |
| `canonical_hash.go` | pcs-core canonical JSON digest |
| `status_transition.go` | PCS status transition policy |
| `array_checks.go` | v0.1 `runtime_receipts` / `certificates` cardinality |
| `schema_validate.go` | JSON Schema validation (all pcs-core schemas) |
| `signed_bundle.go` | Sign + inspect integrity (`IntegrityOptions`) |
| `legacy.go` | Legacy detection + offline `MigrateLegacyBundle` |
| `paths.go` | Repo-root path resolution for `tests/pcs/` |
| `schemas/*.json` | Embedded pcs-core mirror |

## Tests

```bash
cd adapters/pcs && go test ./... -count=1
```

Set `PCS_CORE_PATH` for `TestSchemaMirrorMatchesPCSCore`.
