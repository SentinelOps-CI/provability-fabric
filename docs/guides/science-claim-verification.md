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

## Release admission (default path with `--release-mode`)

In **release mode**, PF is the release-chain admission controller. Handoff and registry are **required** (not optional):

| Flag | Artifact | Required in release mode |
|------|----------|--------------------------|
| `--handoff` | `HandoffManifest.v0` only (`pf_handoff.json` forbidden) | Yes, unless `--allow-missing-handoff-for-local-dev` |
| `--registry` | `ArtifactRegistry.v0` | Yes (defaults to `PCS_CORE_PATH/examples/artifact_registry.valid.json`) |
| `--manifest` | `ReleaseManifest.v0` | When writing `--release-chain-result` |
| `--release-chain-result` | Output `ReleaseChainValidationResult.v0` | Optional |
| `--proof-obligations` | `ProofObligation.v0` from pcs-core Lean checks | Yes when admission profile sets `formal_checks.required` |
| `--lean-check-result` | `LeanCheckResult.v0` from pcs-core Lean trust kernel | Yes when admission profile sets `formal_checks.required` |
| `--admission-profile` | Built-in profile id (e.g. `labtrust_qc_release`) | Yes in release mode |

Do **not** pass `ReleaseManifest.v0` to `--registry`; use `--manifest` for release-chain verify.

### Lean trust-envelope (formal checks)

Release admission profiles may require pcs-core Lean outputs. PF does **not** run Lean; it validates `ProofObligation.v0` and `LeanCheckResult.v0` and records `formal.<ObligationKind>` checks in `ReleaseChainValidationResult.v0`.

```bash
RELEASE=tests/pcs/fixtures/labtrust-release
eval "$(bash scripts/pcs-formal-release-args.sh "$RELEASE")"

pf verify science-claim "$RELEASE/science_claim_bundle.certified.json" \
  --handoff "$RELEASE/handoff_to_pf.json" \
  --registry "$RELEASE/artifact_registry.json" \
  --admission-profile labtrust_qc_release \
  --release-mode \
  $FORMAL_ARGS \
  --out "$RELEASE/verification_result.json"

pf explain release-chain "$RELEASE/release_chain_validation_result.json"
```

Failure codes include `missing_lean_check_result`, `lean_check_failed`, `lean_obligation_mismatch`, `lean_release_id_mismatch`, and `unauthorized_lean_theorem`.

Legacy `pf_handoff.json` is accepted only outside `--release-mode` (a warning is printed). Release mode fails with `legacy_handoff_forbidden_in_release_mode`.

```bash
export PF_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PF_RELEASE_MODE=1

pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --out verification_result.json \
  --release-chain-result release_chain_validation_result.json \
  --release-mode

pf verify release-chain \
  --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --artifact-dir ../pcs-core/examples/labtrust-release \
  --out release_chain_validation_result.json \
  --release-mode

pf explain failure verification_result.json
pf explain release-chain release_chain_validation_result.json
```

Release-chain validation emits schema-valid `ReleaseChainValidationResult.v0` with check IDs including: `manifest_hashes_match`, `producer_commits_match`, `certificate_id_consistent`, `trace_hash_consistent`, `signed_input_bundle_hash_match`, `scientific_memory_import_passed`, `registry_artifact_registered`, `registry_schema_matches`, `registry_producer_allowed`, `registry_status_allowed`, `registry_required_fields_present`, `registry_semantic_checks_executed`, and `registry_admission_passed`.

## Admission benchmark

Measure PF as the PCS release admission controller (valid admits, invalid rejects, localization, explain quality, registry coverage). See [pcs-admission-benchmark.md](pcs-admission-benchmark.md).

```bash
pf benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry ../pcs-core/examples/artifact_registry.valid.json \
  --out benchmark_runs/labtrust_admission \
  --json-summary
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
| 12 | `artifact_registry_admission` | Bundle matches ArtifactRegistry.v0 (fails in release mode without `--registry`) |
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

- Embeds the certified `science_claim_bundle` and `verification_result`
- `signed_input_bundle_hash`: raw file SHA-256 of the certified bundle JSON

## Layout

```
adapters/pcs/                  # verification engine
core/cli/pf/cmd/                 # pf verify | sign | inspect | validate | explain
config/schemas/pcs/            # pcs-core mirror
tests/pcs/fixtures/labtrust/   # LabTrust certified + signed reference fixtures
tests/pcs/fixtures/labtrust-release/  # RC-synced release chain fixtures
tools/pcs-validate/            # fixture matrix validator
scripts/pcs-schema-diff.sh
scripts/pcs-schema-sync.sh
```

## CI and local gates

```bash
make test-pcs-full              # unit + CLI + RC lock + Phase 2 + fixture matrix
make test-pcs
make test-pcs-rc-gate
make test-pcs-phase2
make sync-pcs-rc-fixtures       # refresh labtrust-release from pcs-core RC
make validate-pcs-fixtures   # 29 artifacts including Phase 2 protocol fixtures
make validate-pcs-schema-diff
make freeze-pcs-labtrust-signed   # rewrite tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json (required after canonical JSON / check-list changes)
just pcs-schema-diff
```

```bash
pf validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
pf validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
pf validate artifact-registry tests/pcs/fixtures/labtrust-release/artifact_registry.json
pf validate release-chain-result tests/pcs/fixtures/labtrust-release/release_chain_validation_result.json
```

## LabTrust release fixtures

LabTrust release fixtures (`tests/pcs/fixtures/labtrust-release/`): certified bundle from `LabTrust-Gym/examples/pcs_qc_release/release/science_claim_bundle.certified.json` (`scb-pcs-qc-release-v0.1`), plus PF-generated `verification_result.json` and `signed_science_claim_bundle.json`. Regenerate with `make freeze-pcs-labtrust-release` (requires LabTrust-Gym beside this repo). Freeze scripts set `PF_SOURCE_COMMIT` to `git rev-parse HEAD`, enable `--release-mode`, and reject placeholder commits (`cccc…`, `aaaa…`, etc.) on PF outputs.

Sync from pcs-core:

```bash
make sync-pcs-rc-fixtures
```
