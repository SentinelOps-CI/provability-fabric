# Science claim verification (PCS v0.1)

Provability Fabric verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts from the LabTrust proof-carrying lab workflow.

## Canonical bundle shape (pcs-core)

Provability Fabric does **not** accept legacy PF-only shapes. Bundles must use:

| Field | pcs-core canonical |
|-------|-------------------|
| `schema_version` | `"v0"` (not `"ScienceClaimBundle.v0"`) |
| Runtime evidence | `runtime_receipts[]` (not `runtime_receipt`) |
| Certificates | `certificates[]` (not `trace_certificate`) |
| Policy | `verification_policy` with `policy_id` and `required_checks` |

LabTrust reference fixtures live under `tests/pcs/fixtures/labtrust/` (copied from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) examples).

## Commands

```bash
# From repository root (recommended)
make demo-pcs

# Wrapper (Git Bash / WSL)
./pf verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
./pf sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json --out tests/pcs/signed_science_claim_bundle.demo.json
./pf inspect science-claim tests/pcs/signed_science_claim_bundle.demo.json --strict
./pf inspect science-claim tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json --reverify
./pf migrate science-claim tests/pcs/invalid_legacy_singular_runtime_receipt.json --out /tmp/migrated.json

# Or: go -C (PowerShell, cmd, Git Bash)
go -C core/cli/pf run . verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
```

Paths like `tests/pcs/<file>.json` resolve to the repo-root `tests/pcs/` directory even when the Go module cwd is `core/cli/pf`.

### Inspect flags

| Flag | Purpose |
|------|---------|
| `--strict` | Require PF-computed `verification_result` and wrapper digests (pf sign output) |
| `--reverify` | Re-run the full 17-check PF verifier on the embedded `science_claim_bundle` (exits non-zero if re-verification fails) |
| `--json` | Emit `VerificationResult` JSON (with `--reverify`, emits embedded + reverified) |

LabTrust-exported signed bundles load without `--strict` (external digest rules). Use `--reverify` to confirm PF checks on the embedded bundle.

Use `--local-dev` on verify/sign only for bundles with `local_dev: true` or the 40-zero `source_commit` placeholder.

## Release admission (Phase 2)

```bash
# HandoffManifest.v0 or legacy pf_handoff.json
pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --release-mode

# ReleaseManifest.v0 artifact registry (until ArtifactRegistry.v0 ships in pcs-core)
pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --registry tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --release-mode

# Release chain validation (PF admission artifacts; colocate manifest with artifacts)
pf verify release-chain \
  --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --artifact-dir ../pcs-core/examples/labtrust-release \
  --out /tmp/release_chain_validation_result.json
```

## Seventeen required checks

| # | check_id | Description |
|---|----------|-------------|
| 1 | `science_claim_bundle_schema` | ScienceClaimBundle.v0 schema valid (pcs-core) |
| 2 | `claim_artifact_present` | ClaimArtifact.v0 exists |
| 3 | `assumption_set_present` | AssumptionSet.v0 exists |
| 4 | `runtime_receipt_present` | Exactly one RuntimeReceipt in `runtime_receipts` (v0.1) |
| 5 | `trace_certificate_present` | At least one TraceCertificate in `certificates` |
| 6 | `evidence_bundle_present` | EvidenceBundle.v0 exists |
| 7 | `assumption_set_ref_match` | Claim refs match assumption set id |
| 8 | `runtime_trace_hash_present` | `runtime_receipts[0].trace_hash` non-empty |
| 9 | `trace_hash_alignment` | Certificate trace_hash matches receipt |
| 10 | `certificate_status_checked` | TraceCertificate.status is CertificateChecked |
| 11 | `status_transition_policy` | PCS status transitions allow ProofChecked only from admissible states |
| 12 | `artifact_registry_admission` | Bundle matches ReleaseManifest.v0 registry (skipped without `--registry`) |
| 13 | `evidence_refs_complete` | Evidence refs claim, assumption set, receipt, certificate |
| 14 | `artifact_not_stale` | No required artifact has status Stale |
| 15 | `source_provenance_present` | source_repo and source_commit present |
| 16 | `signature_or_digest_present` | signature_or_digest present |
| 17 | `source_commit_not_placeholder` | No 40-zero source_commit in release mode |

## Output for Scientific Memory

**VerificationResult** (`schema_version`: `v0`):

- `verification_id`: `verification-<uuid>`
- `status`: `ProofChecked` when all checks pass, `Rejected` otherwise (pcs-core `artifact_status` enum)
- `checks[].details`: JSON object (may include `reason_code`)
- `signature_or_digest`: `sha256:<64-hex>` (PF canonical JSON digest)

**SignedScienceClaimBundle** (`schema_version`: `v0`):

- `science_claim_bundle`
- `verification_result`
- `signer`: `Provability Fabric`
- `signed_bundle_id`: `signed-<uuid>`
- `signature_or_digest`: `sha256:<64-hex>`

Signing is refused when verification status is not `ProofChecked`.

## Schema sync with pcs-core

Schemas under `config/schemas/pcs/` must match [pcs-core/schemas](https://github.com/SentinelOps-CI/pcs-core/tree/main/schemas) exactly. Embedded copies live in `adapters/pcs/schemas/`.

```bash
# Compare against sibling checkout (default ../pcs-core)
just pcs-schema-diff
# or
make validate-pcs-schema-diff PCS_CORE_PATH=../pcs-core
bash scripts/pcs-schema-diff.sh /path/to/pcs-core

# Refresh mirrors after pcs-core schema changes (updates config/ and adapters/pcs/schemas/)
just pcs-schema-sync
make sync-pcs-schemas PCS_CORE_PATH=../pcs-core
```

## Layout

```
config/schemas/pcs/          # pcs-core mirror (HandoffManifest, ReleaseManifest, ReleaseChainValidationResult, …)
adapters/pcs/                  # verification engine + embedded schemas
core/cli/pf/cmd/               # pf verify|sign|inspect science-claim
tests/pcs/fixtures/labtrust/   # LabTrust certified + signed reference fixtures
tools/pcs-validate/            # fixture matrix validator
scripts/pcs-schema-diff.sh
scripts/pcs-schema-sync.sh
```

## Tests and CI

```bash
make test-pcs
make validate-pcs-fixtures   # 28 artifacts including Phase 2 protocol fixtures
make validate-pcs-schema-diff
make freeze-pcs-labtrust-signed   # rewrite tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json (required after canonical JSON / check-list changes)
just pcs-schema-diff
```

LabTrust release fixtures (`tests/pcs/fixtures/labtrust-release/`): certified bundle from `LabTrust-Gym/examples/pcs_qc_release/release/science_claim_bundle.certified.json` (`scb-pcs-qc-release-v0.1`), plus PF-generated `verification_result.json` and `signed_science_claim_bundle.json`. Regenerate with `make freeze-pcs-labtrust-release` (requires LabTrust-Gym beside this repo). Freeze scripts set `PF_SOURCE_COMMIT` to `git rev-parse HEAD`, enable `--release-mode`, and reject placeholder commits (`cccc…`, `aaaa…`, etc.) on PF outputs.

```bash
pf validate verification-result tests/pcs/fixtures/labtrust-release/verification_result.json
pf validate signed-science-claim tests/pcs/fixtures/labtrust-release/signed_science_claim_bundle.json
pf validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
pf validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
pf validate release-chain-result tests/pcs/fixtures/labtrust-release/release_chain_validation_result.json
```

LabTrust freeze fixtures under `tests/pcs/fixtures/labtrust/`:

| File | Role |
|------|------|
| `science_claim_bundle.certified.json` | Canonical pcs-core certified bundle (verify must be `ProofChecked`) |
| `signed_science_claim_bundle.json` | PF-signed wrapper (`pf sign` output; strict inspect; RC bundles may embed 15 checks) |
| `signed_science_claim_bundle.labtrust-export.json` | External LabTrust export (2 embedded checks; use `inspect --reverify`) |

CI: `.github/workflows/pcs-ci.yml` (checks out pcs-core, runs schema diff, fixture matrix, LabTrust freeze validation, CLI smoke).

## Legacy migration (offline only)

`pf verify` rejects bundles with `runtime_receipt`, `trace_certificate`, artifact-name `schema_version` values (for example `ScienceClaimBundle.v0`), or other non-canonical top-level keys.

```bash
./pf migrate science-claim tests/pcs/invalid_legacy_singular_runtime_receipt.json --out /tmp/migrated.json
./pf verify science-claim /tmp/migrated.json
```

Go API: `pcs.MigrateLegacyBundle()` for programmatic migration.

## Rigorous guarantees

- Schemas are embedded in `adapters/pcs` and drift-tested against `config/schemas/pcs/` and pcs-core.
- Failed checks include `details.reason_code` (for example `PCS_LEGACY_BUNDLE_FORMAT`, `PCS_RUNTIME_RECEIPT_COUNT`, `PCS_TRACE_HASH_MISMATCH`).
- All certificates are verified for hash alignment and `CertificateChecked`.
- `pf verify` exits `1` on failure and prints `check_id: reason_code` lines to stderr.
