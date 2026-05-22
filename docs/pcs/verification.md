# Science claim verification

Provability Fabric verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts from the proof-carrying lab workflow.

## Canonical bundle shape

Provability Fabric does not accept legacy bundle shapes. Bundles must use:

| Field | Required shape |
|-------|----------------|
| `schema_version` | `"v0"` |
| Runtime evidence | `runtime_receipts[]` (exactly one receipt in v0.1) |
| Certificates | `certificates[]` |
| Policy | `verification_policy` with `policy_id` and `required_checks` |

Reference conformance fixtures: `tests/pcs/fixtures/labtrust/` (from [pcs-core](https://github.com/SentinelOps-CI/pcs-core) examples).

## Basic commands

```bash
make demo-pcs

./pf verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
./pf sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json \
  --out tests/pcs/signed_science_claim_bundle.demo.json
./pf inspect science-claim tests/pcs/signed_science_claim_bundle.demo.json --strict
./pf migrate science-claim tests/pcs/invalid_legacy_singular_runtime_receipt.json --out /tmp/migrated.json
```

Paths like `tests/pcs/<file>.json` resolve from the repository root even when the CLI runs from `core/cli/pf`.

### Inspect flags

| Flag | Purpose |
|------|---------|
| `--strict` | Require PF-computed verification result and wrapper digests |
| `--reverify` | Re-run all 17 checks on the embedded bundle |
| `--json` | Emit verification result JSON |

Use `--local-dev` only for bundles marked for local development.

## Release mode

With `--release-mode`, Provability Fabric acts as the release admission controller. Handoff and registry are required:

| Flag | Artifact | Required in release mode |
|------|----------|--------------------------|
| `--handoff` | `HandoffManifest.v0` (legacy `pf_handoff.json` is rejected) | Yes |
| `--registry` | `ArtifactRegistry.v0` | Yes |
| `--manifest` | `ReleaseManifest.v0` | For release-chain verify |
| `--admission-profile` | Built-in profile ID | Yes |
| `--proof-obligations` | `ProofObligation.v0` | When profile requires formal checks |
| `--lean-check-result` | `LeanCheckResult.v0` | When profile requires formal checks |

Do not pass `ReleaseManifest.v0` to `--registry`; use `--manifest` for release-chain verification.

### Formal checks (Lean trust envelope)

Provability Fabric does not run Lean. It validates `ProofObligation.v0` and `LeanCheckResult.v0` supplied by pcs-core and records `formal.<ObligationKind>` checks in the release-chain validation result.

```bash
RELEASE=tests/pcs/fixtures/labtrust-release
eval "$(bash scripts/pcs-formal-release-args.sh "$RELEASE")"

pf verify science-claim "$RELEASE/science_claim_bundle.certified.json" \
  --handoff "$RELEASE/handoff_to_pf.json" \
  --registry "$RELEASE/artifact_registry.json" \
  --admission-profile labtrust_qc_release \
  --release-mode \
  $FORMAL_ARGS

pf explain release-chain "$RELEASE/release_chain_validation_result.json"
```

### Full release verify example

```bash
export PF_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PF_RELEASE_MODE=1

pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --admission-profile labtrust_qc_release \
  --release-mode \
  --out verification_result.json \
  --release-chain-result release_chain_validation_result.json

pf verify release-chain \
  --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --artifact-dir tests/pcs/fixtures/labtrust-release \
  --admission-profile labtrust_qc_release \
  --release-mode \
  --out release_chain_validation_result.json

pf explain failure verification_result.json
pf explain release-chain release_chain_validation_result.json
```

Release-chain validation emits `ReleaseChainValidationResult.v0` with checks such as `manifest_hashes_match`, `registry_admission_passed`, `registry_semantic_checks_executed`, and formal check IDs when applicable.

## Seventeen consistency checks

| # | check_id | Description |
|---|----------|-------------|
| 1 | `science_claim_bundle_schema` | Bundle schema valid |
| 2 | `claim_artifact_present` | Claim artifact exists |
| 3 | `assumption_set_present` | Assumption set exists |
| 4 | `runtime_receipt_present` | Exactly one runtime receipt |
| 5 | `trace_certificate_present` | At least one trace certificate |
| 6 | `evidence_bundle_present` | Evidence bundle exists |
| 7 | `assumption_set_ref_match` | Claim refs match assumption set |
| 8 | `runtime_trace_hash_present` | Receipt trace hash non-empty |
| 9 | `trace_hash_alignment` | Certificate trace hash matches receipt |
| 10 | `certificate_status_checked` | Certificate status is checked |
| 11 | `status_transition_policy` | Status transitions allow proof-checked only from admissible states |
| 12 | `artifact_registry_admission` | Bundle matches artifact registry |
| 13 | `evidence_refs_complete` | Evidence refs complete |
| 14 | `artifact_not_stale` | No required artifact is stale |
| 15 | `source_provenance_present` | Source repo and commit present |
| 16 | `signature_or_digest_present` | Digest present |
| 17 | `source_commit_not_placeholder` | No placeholder commit in release mode |

Older signed fixtures may show 15 embedded checks from an earlier generation commit; new sign output always embeds 17.

## Outputs for Scientific Memory

**VerificationResult** (`schema_version`: `v0`):

- `status`: `ProofChecked` or `Rejected`
- `checks[].details`: structured failure information
- `signature_or_digest`: canonical JSON digest

**SignedScienceClaimBundle** (`schema_version`: `v0`):

- Embeds certified bundle and verification result
- `signed_input_bundle_hash`: SHA-256 of the certified bundle file

## Admission profiles

| Profile ID | Use case |
|------------|----------|
| `labtrust_qc_release` | Hospital lab QC release |
| `agent_tool_use_safety` | Agent tool-use safety |
| `scientific_computation_reproducibility` | Reproducible computation workflows |

Profile JSON files: `adapters/pcs/admission_profiles/`.

## Validate protocol artifacts

```bash
pf validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
pf validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
pf validate artifact-registry tests/pcs/fixtures/labtrust-release/artifact_registry.json
pf validate release-chain-result tests/pcs/fixtures/labtrust-release/release_chain_validation_result.json
```

## Local gates

```bash
make test-pcs-full
make test-pcs
make validate-pcs-fixtures
make validate-pcs-schema-diff
```

See [Admission benchmarks](admission-benchmarks.md) for measuring admission controller quality.
