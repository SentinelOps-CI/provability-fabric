# Science claim verification (PCS v0.1)

Provability Fabric verifies and signs `ScienceClaimBundle.v0` artifacts produced by the LabTrust-Gym and CertifyEdge proof-carrying lab workflow.

## Commands

```bash
pf verify science-claim science_claim_bundle.certified.json
pf sign science-claim science_claim_bundle.certified.json --out signed_science_claim_bundle.json
pf inspect science-claim signed_science_claim_bundle.json
```

Use `--json` on verify or inspect to emit machine-readable `VerificationResult.v0` JSON.

## Required checks (exactly 14)

Verification emits exactly fourteen checks in a stable order (`pcs.RequiredCheckIDs` in `adapters/pcs/checks_registry.go`):

1. `ScienceClaimBundle.v0` schema validity
2. `ClaimArtifact.v0` present
3. `AssumptionSet.v0` present
4. `RuntimeReceipt.v0` present
5. `TraceCertificate.v0` present
6. `EvidenceBundle.v0` present
7. `ClaimArtifact.assumption_set_ref` matches included `AssumptionSet`
8. `RuntimeReceipt.trace_hash` present
9. `TraceCertificate.trace_hash` matches `RuntimeReceipt.trace_hash`
10. `TraceCertificate.status` is `CertificateChecked`
11. `EvidenceBundle` references included artifacts
12. No major artifact has status `Stale`
13. `source_repo` and `source_commit` on all major artifacts
14. `signature_or_digest` on all major artifacts

## Output

Successful verification emits `VerificationResult.v0` with `status: passed`. Any failed required check sets `status: failed`.

Signing is allowed only when verification passes. The signed wrapper (`SignedScienceClaimBundle.v0`) is importable by Scientific Memory without re-running Provability Fabric.

## Fixtures

Development fixtures live under `tests/pcs/`:

- `valid_labtrust_bundle.json` — passing LabTrust demo bundle
- `invalid_missing_assumption.json`
- `invalid_missing_certificate.json`
- `invalid_mismatched_trace_hash.json`
- `invalid_rejected_certificate.json`
- `invalid_stale_artifact.json`

Run adapter tests from the repository root:

```bash
make test-pcs
```

Or:

```bash
cd adapters/pcs && go test ./...
cd core/cli/pf && go test ./cmd/...
```

CI: `.github/workflows/pcs-ci.yml` runs adapter tests, CLI tests, smoke verify/sign/inspect, and rejects signing failed bundles.

## Rigorous guarantees

- Input bundles are validated against `config/schemas/pcs/ScienceClaimBundle.v0.schema.json`.
- Output `VerificationResult.v0` is validated against its schema before return.
- Signed wrappers are validated against `SignedScienceClaimBundle.v0.schema.json` and digests are recomputed on inspect.
- Artifact digests use canonical JSON (sorted object keys) for cross-tool stability.
