# Science claim verification (PCS v0.1)

Provability Fabric verifies and signs `ScienceClaimBundle.v0` artifacts from the LabTrust proof-carrying lab workflow.

## Commands

```bash
# From repository root (recommended)
make demo-pcs

# Wrapper (Git Bash / WSL)
./pf verify science-claim tests/pcs/valid_labtrust_bundle.json
./pf sign science-claim tests/pcs/valid_labtrust_bundle.json --out tests/pcs/signed_science_claim_bundle.demo.json
./pf inspect science-claim tests/pcs/signed_science_claim_bundle.demo.json

# Or: go -C (PowerShell, cmd, Git Bash)
go -C core/cli/pf run . verify science-claim tests/pcs/valid_labtrust_bundle.json
```

Paths like `tests/pcs/<file>.json` always resolve to the repo-root `tests/pcs/` directory (sign output included), even when the Go module cwd is `core/cli/pf`. Do not use `../../tests/pcs/...` from `core/cli/pf` — that used to create a shadow tree under `core/cli/pf/tests/`.

Use `--json` on verify or inspect for machine-readable output. Use `--local-dev` only for local bundles that set `local_dev: true` or use the 40-zero `source_commit` placeholder.

## Fifteen required checks

| # | check_id | Description |
|---|----------|-------------|
| 1 | `science_claim_bundle_schema` | ScienceClaimBundle.v0 schema valid |
| 2 | `claim_artifact_present` | ClaimArtifact.v0 exists |
| 3 | `assumption_set_present` | AssumptionSet.v0 exists |
| 4 | `runtime_receipt_present` | RuntimeReceipt.v0 exists |
| 5 | `trace_certificate_present` | At least one TraceCertificate.v0 exists |
| 6 | `evidence_bundle_present` | EvidenceBundle.v0 exists |
| 7 | `assumption_set_ref_match` | Claim refs match assumption set id |
| 8 | `runtime_trace_hash_present` | RuntimeReceipt.trace_hash non-empty |
| 9 | `trace_hash_alignment` | Certificate trace_hash matches receipt |
| 10 | `certificate_status_checked` | TraceCertificate.status is CertificateChecked |
| 11 | `evidence_refs_complete` | Evidence references claim, assumption, receipt, certificate |
| 12 | `artifact_not_stale` | No required artifact has status Stale |
| 13 | `source_provenance_present` | source_repo and source_commit present |
| 14 | `signature_or_digest_present` | signature_or_digest present |
| 15 | `source_commit_not_placeholder` | No 40-zero source_commit in release mode |

## Output for Scientific Memory

**VerificationResult** (`schema_version`: `v0`):

- `verification_id`: `verification-<uuid>`
- `checks[].details`: JSON object (may be empty `{}`)
- `signature_or_digest`: `sha256:...` (canonical JSON digest)

**SignedScienceClaimBundle** (`schema_version`: `v0`):

- `science_claim_bundle`
- `verification_result`
- `signer`: `Provability Fabric`
- `signed_bundle_id`: `signed-<uuid>`
- `signature_or_digest`: `sha256:...`

Signing is refused when `verification_result.status` is `failed`.

## Layout

```
config/schemas/pcs/          # VerificationResult + SignedScienceClaimBundle schemas
adapters/pcs/                # verification engine
core/cli/pf/cmd/             # pf verify|sign|inspect science-claim
tests/pcs/                   # LabTrust fixtures
```

## Tests

```bash
make test-pcs
```

CI: `.github/workflows/pcs-ci.yml`

## Rigorous guarantees

- Schemas are embedded in `adapters/pcs` (drift-tested against `config/schemas/pcs/`).
- Failed checks include `details.reason_code` (for example `PCS_TRACE_HASH_MISMATCH`).
- All trace certificates are verified for hash alignment and `CertificateChecked`.
- `pf verify` exits `1` on failure and prints `check_id: reason_code` lines to stderr.
- `make validate-pcs-fixtures` runs the full valid/invalid fixture matrix via `tools/pcs-validate`.
