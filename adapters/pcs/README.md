# PCS adapter (Provability Fabric)

Verifies and signs **pcs-core canonical** `ScienceClaimBundle.v0` artifacts for the Proof-Carrying Lab Workflow v0.1.

## Responsibilities

- Load LabTrust-certified science claim bundles (`runtime_receipts[]`, `certificates[]`, `schema_version: "v0"`)
- Reject legacy singular-field PF bundles at load and schema validation
- Run 17 consistency, provenance, registry, and status-transition checks
- Enforce release-mode admission: mandatory admission profile, `HandoffManifest.v0`, and `ArtifactRegistry.v0`
- Load workflow admission profiles from `admission_profiles/` (`schema.json`, `labtrust_qc_release`, `agent_tool_use_safety`)
- Emit schema-valid `ReleaseChainValidationResult.v0` with stable release-chain check IDs
- Emit `VerificationResult.v0` with `ProofChecked` / `Rejected` status
- Build `SignedScienceClaimBundle.v0` wrappers for Scientific Memory import

## Usage (via CLI)

```bash
./pf verify science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json
./pf verify science-claim tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --admission-profile labtrust_qc_release \
  --release-mode
./pf verify release-chain \
  --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --artifact-dir ../pcs-core/examples/labtrust-release \
  --admission-profile labtrust_qc_release \
  --out /tmp/release_chain_validation_result.json \
  --release-mode
./pf sign science-claim tests/pcs/fixtures/labtrust/science_claim_bundle.certified.json --out /tmp/signed.json
./pf inspect science-claim /tmp/signed.json --strict
./pf explain failure /tmp/verification_result.json
./pf explain release-chain /tmp/release_chain_validation_result.json
./pf validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
./pf validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
./pf validate artifact-registry tests/pcs/fixtures/labtrust-release/artifact_registry.json
```

Canonical artifact vocabulary: [pcs-core](https://github.com/SentinelOps-CI/pcs-core).

## Package layout

| File | Role |
|------|------|
| `bundle_validator.go` | 17-check verification pipeline |
| `artifact_registry.go` | ArtifactRegistry.v0 loader |
| `handoff_manifest.go` | HandoffManifest.v0 + legacy `pf_handoff.json` |
| `release_chain_validation.go` | ReleaseChainValidationResult.v0 emission |
| `release_manifest.go` | ReleaseManifest.v0 loader |
| `admission_profile.go` | Admission profiles + release-mode profile resolution |
| `tool_use_admission.go` | Agent tool-use admission skeleton |
| `release_mode.go` | Release-mode admission policy |
| `registry_semantic_audit.go` | Auditable registry semantic check execution |
| `registry_validate.go` | ArtifactRegistry.v0 bundle + manifest admission |
| `registry_release_chain.go` | Granular registry_* release-chain checks |
| `explain.go` | Actionable failure explanations |
| `canonical_hash.go` | pcs-core canonical JSON digest |
| `status_transition.go` | PCS status transition policy |
| `array_checks.go` | v0.1 `runtime_receipts` / `certificates` cardinality |
| `schema_validate.go` | JSON Schema validation (all pcs-core schemas) |
| `signed_bundle.go` | Sign + inspect integrity (`IntegrityOptions`) |
| `legacy.go` | Legacy detection + offline `MigrateLegacyBundle` |
| `paths.go` | Repo-root path resolution for `tests/pcs/` |
| `schemas/*.json` | Embedded pcs-core mirror |

## PCS admission benchmarks (pcs-bench)

PF is the reference **release admission controller** benchmark runner. It emits a pcs-core bundle under `--out`:

- `benchmark_report.v0.json`, `benchmark_run.v0.json`, `failure_localization_result.v0.json`, `coverage_report.v0.json`, `explain_quality_report.v0.json`
- Normalized paths: `explain_quality/`, `failure_localization/`, `coverage/`, `runs/`, `logs/`
- `pcs_bench_ingest.v0.json` — **PcsBenchIngest.v0** import manifest for **pcs-bench** (embedded runs/coverage/explain/FLR/profile coverage, `artifact_refs`, semantic validation)

```bash
python scripts/materialize-admission-benchmark-cases.py
bash scripts/pf.sh benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --out benchmark_runs/labtrust_admission \
  --validate --validate-pcs-core-output ../pcs-core
```

See [docs/guides/pcs-admission-benchmark.md](../../docs/guides/pcs-admission-benchmark.md).

## Tests

```bash
cd adapters/pcs && go test ./... -count=1
```

Set `PCS_CORE_PATH` for `TestSchemaMirrorMatchesPCSCore` and `TestBenchmarkBundleValidatesAgainstPCSCore`.
