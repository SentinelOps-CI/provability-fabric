# PCS adapter (Provability Fabric)

Verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts for the Proof-Carrying Lab Workflow v0.1.

## Responsibilities

- Load LabTrust-certified science claim bundles (`runtime_receipts[]`, `certificates[]`, `schema_version: "v0"`)
- Reject legacy singular-field PF bundles at load and schema validation
- Run 15 consistency and provenance checks
- Emit `VerificationResult.v0` with `ProofChecked` / `Rejected` status
- Build `SignedScienceClaimBundle.v0` wrappers for Scientific Memory import

## Usage (via CLI)

```bash
./pf verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
./pf sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json --out /tmp/signed.json
./pf inspect science-claim /tmp/signed.json --strict
./pf inspect science-claim tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json --reverify
```

Canonical artifact vocabulary: [pcs-core](https://github.com/SentinelOps-CI/pcs-core).

## Package layout

| File | Role |
|------|------|
| `bundle_validator.go` | 15-check verification pipeline |
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
