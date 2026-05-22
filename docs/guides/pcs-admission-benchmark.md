# PCS admission benchmark

Provability Fabric exposes a **release admission benchmark** that measures whether PF acts correctly as the PCS release admission controller: valid releases are admitted, invalid releases are rejected, failures are localized, and `pf explain` output is useful.

## Layout

Benchmark cases live under `benchmarks/admission/`:

| Workflow | Directory | Profile |
|----------|-----------|---------|
| LabTrust QC release | `labtrust_qc_release/` | `labtrust_qc_release` |
| Formal trust-kernel enforcement | `formal_trust_kernel/` | `labtrust_qc_release` (formal-focused invalid cases) |
| Agent tool-use safety | `tool_use_safety/` | `agent_tool_use_safety` |
| Scientific computation reproducibility | `computation_reproducibility/` | `scientific_computation_reproducibility` |

Each workflow has:

- `workflow.json` — defaults (fixture root, registry, handoff, formal artifacts)
- `valid/` — cases that must **admit**
- `invalid/` — cases that must **reject** with expected failure codes

Regenerate case JSON from fixtures:

```bash
python scripts/materialize-admission-benchmark-cases.py
```

## Run benchmarks

If `pf` is not on your PATH (common on Git Bash / Windows), use the repo wrapper (builds `core/cli/pf/pf.exe` when Go is available):

```bash
bash scripts/pf.sh benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry ../pcs-core/examples/artifact_registry.valid.json \
  --out benchmark_runs/labtrust_admission \
  --validate \
  --validate-pcs-core-output ../pcs-core \
  --json-summary
```

Or from `core/cli/pf` with Go on PATH:

```bash
cd core/cli/pf && go run . benchmark admission \
  --cases ../../benchmarks/admission/labtrust_qc_release \
  --registry ../../../pcs-core/examples/artifact_registry.valid.json \
  --out ../../benchmark_runs/labtrust_admission \
  --validate
```

When `pf` is installed globally, the same flags work as `pf benchmark admission ...`.

All workflows (CI / local gate):

```bash
bash scripts/pcs-benchmark-admission.sh
```

Or via Make:

```bash
make test-pcs-benchmark
```

pcs-bench producer gate (labtrust ingest + validation):

```bash
make pcs-bench-producer
```

On Windows (Git Bash), `bash scripts/pf.sh` builds `core/cli/pf/pf.exe` automatically when Go is installed. Benchmark shell scripts use the same resolver. You can also run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts/pcs-benchmark-admission.ps1
```

## Outputs

Each run writes a **pcs-core benchmark bundle** under `--out` (validated against `config/schemas/pcs/`):

| Path | Schema | Role |
|------|--------|------|
| `benchmark_report.v0.json` | `BenchmarkReport.v0` | Suite aggregate (summary, coverage block, run refs) |
| `benchmark_run.v0.json` | `BenchmarkRun.v0` (array) | Per-case runs |
| `failure_localization_result.v0.json` | `FailureLocalizationResult.v0` (array) | Per invalid-case localization |
| `coverage_report.v0.json` | `CoverageReport.v0` (array) | Per-metric coverage |
| `explain_quality_report.v0.json` | `ExplainQualityReport.v0` (array) | Per invalid-case explain scoring |
| `explain_quality/<case_id>.explain_quality_report.v0.json` | `ExplainQualityReport.v0` | Per-case pcs-core explain export |
| `failure_localization/<case_id>.failure_localization_result.v0.json` | `FailureLocalizationResult.v0` | Per-case failure localization |
| `coverage/registry_coverage_report.v0.json` | `CoverageReport.v0` | Registry coverage |
| `coverage/formal_check_coverage_report.v0.json` | `CoverageReport.v0` | Formal-check coverage |
| `coverage/admission_profile_coverage_report.v0.json` | `CoverageReport.v0` | Admission profile coverage |
| `coverage/release_reproducibility_coverage_report.v0.json` | `CoverageReport.v0` | Release reproducibility coverage |
| `coverage/admission_profile.profile_coverage_report.v0.json` | `ProfileCoverageReport.v0` | Profile-level coverage (also in ingest `profile_coverage_reports`) |
| `commands.json` | — | Command log for reproducibility |
| `logs/run.log` | — | Case outcome log |
| `runs/<case_id>/` | — | Per-case copies of run / explain / FLR artifacts |
| `pcs_bench_ingest.v0.json` | `PcsBenchIngest.v0` | **Single-file pcs-bench import** (`producer_id`, `suite_id`, `workflow_id`, runs, coverage, explain, FLR, profile coverage, commands, logs, optional `artifact_refs`) |
| `admission_benchmark_suite.v0.json` | PF-internal | Suite metrics + case outcomes (legacy PF summary) |

Use `--json-summary` to print a compact JSON summary on stdout (`producer_id`, `suite_id`, `workflow_id`, `cases_run`, `cases_passed`, `failure_localization_accuracy`, `explain_quality_score`, `registry_coverage_score`, `formal_check_coverage_score`, `pcs_bench_ingest_path`, plus legacy `metrics` / `run_id` fields).

### Metrics (`admission_benchmark_suite.v0.json` → `metrics`)

| Metric | Meaning |
|--------|---------|
| `valid_release_admission_rate` | Share of `valid/` cases that admitted |
| `invalid_release_rejection_rate` | Share of `invalid/` cases that rejected with matching codes |
| `failure_localization_accuracy` | Share of localized invalid cases where observed check ID, responsible component (`hashing`, `handoff`, `scientific_memory`, …), and artifact path match `localization` |
| `failure_code_accuracy` | Share of invalid cases whose observed codes match `expect_failure_codes` |
| `explain_output_completeness` | Mean explain field completeness for release-chain invalid cases |
| `registry_check_coverage` | Required profile registry checks observed in RCVR |
| `admission_profile_coverage` | Profile + registry check exercise on valid release-chain runs |
| `formal_check_enforcement_coverage` | Formal invalid cases rejected with expected codes |

### Registry coverage

PF-internal `coverage_report` in `admission_benchmark_suite.v0.json` and pcs-core `CoverageReport.v0` metrics in the bundle `coverage_report.v0.json` array include registry counters from the valid release-chain RCVR:

- `registered_artifacts_checked`
- `required_fields_checked`
- `allowed_statuses_checked`
- `semantic_checks_executed` / `deferred` / `skipped`
- `release_blocking_checks_passed` / `failed`

### Explain quality

For invalid cases with `explain_requirements`, PF emits pcs-core `ExplainQualityReport.v0` per case with all canonical sections (`provenance`, `hashes`, `handoffs`, `verification`, `formal_checks`, `limitations`, `lineage`, `repair_hints`), scored from failure code, artifact path, expected/actual values, responsible component, repair hints, and optional registry/handoff/formal references.

Formal trust-kernel enforcement (proof obligations, Lean checks, theorem references) is exercised primarily in the **LabTrust QC release** workflow invalid cases (`missing_proof_obligation`, `failed_lean_check`, etc.).

## pcs-bench integration

Downstream **pcs-bench** should read **`pcs_bench_ingest.v0.json`** (`PcsBenchIngest.v0`: runs, `coverage_reports`, `explain_quality_reports`, `failure_localization_reports`, `profile_coverage_reports`, `commands`, `logs`, provenance). The same artifacts are also laid out on disk under normalized paths (`explain_quality/`, `coverage/`, `runs/`, `logs/`, plus `benchmark_report.v0.json` for suite aggregates). Schemas are synced from pcs-core into `config/schemas/pcs/` and embedded in `adapters/pcs/schemas/`.

Use `--validate-pcs-core-output /path/to/pcs-core` to validate every normalized artifact against the canonical pcs-core `schemas/` tree (in addition to `--validate` against PF’s synced copy).

Validate a bundle directory (CI / local gate):

```bash
make validate-pcs-benchmark-bundle
# or (pcs validate compatible):
bash scripts/pcs-validate-benchmark-bundle.sh benchmark_runs/labtrust_admission
# or:
bash scripts/pf.sh validate benchmark-bundle benchmark_runs/labtrust_admission
```

`--validate` on `pf benchmark admission` runs the same bundle gate after every write.

Refresh the committed reference ingest after changing benchmark emit logic or labtrust cases:

```bash
bash scripts/export-pcs-benchmark-ingest-reference.sh
```

CI checks that `benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json` exists and passes `pcs validate`.

Explain export uses `pcs.ExportPCSExplainQualityReport` with PF field → pcs-core section mapping (`verification`, `provenance`, `repair_hints`, `handoffs`, `formal_checks`).

Canonical required invalid case IDs (union across workflows) are listed in `pcs.RequiredAdmissionInvalidCaseIDs`.

Minimum gate thresholds (current PF tests):

- LabTrust: **all cases pass** (`RequireAllCasesPass`), invalid rejection rate = 1.0, valid admission rate = 1.0, per-case explain quality_score ≥ 0.8 when required
- Tool-use / computation: invalid rejection rate ≥ 0.80

### Definition of done (PCS benchmark reference)

| Step | Status |
|------|--------|
| PCS-native explain export (`ExportPCSExplainQualityReport`, all eight canonical sections, per-case files under `explain_quality/`) | Done |
| PCS-native coverage (`coverage/registry_coverage_report.v0.json`, `formal_check_coverage_report.v0.json`, `admission_profile_coverage_report.v0.json`, `release_reproducibility_coverage_report.v0.json`, `ProfileCoverageReport.v0`) | Done |
| `pcs_bench_ingest.v0.json` (`PcsBenchIngest.v0` with embedded arrays + `artifact_refs` digests aligned to embedded `signature_or_digest`) | Done |
| Go semantic gate (`ValidatePCSBenchIngestSemantics`, mirrors pcs-core `validate_pcs_bench_ingest_semantics`) | Done |
| `pf benchmark admission --validate` + `--validate-pcs-core-output` + optional `pcs validate pcs_bench_ingest.v0.json` | Done |
| `--json-summary` with producer/suite/workflow metrics and `pcs_bench_ingest_path` | Done |
| Failure localization gold standard (check-aware components, artifact-path alignment, per-case `failure_localization/`) | Done |
| Required invalid failure families (`RequiredAdmissionInvalidCaseIDs`, incl. `scientific_memory_import_failure`) | Done |
| Committed reference ingest (`benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json`, `pcs validate` + `TestExportPCSBenchIngestReferenceArtifact`) | Done |
| `make pcs-bench-producer` (admission + ingest validation for pcs-bench aggregation) | Done |
| Canonical producer ids (`suite_id`: `pf-labtrust-admission-v0`, `workflow_id`: `hospital_lab.qc_release`) | Done |

## Adding cases

1. Add or extend fixtures under `tests/pcs/fixtures/`.
2. Add a case entry in `scripts/materialize-admission-benchmark-cases.py`.
3. Run `python scripts/materialize-admission-benchmark-cases.py`.
4. Run `make test-pcs-benchmark`, `bash scripts/pcs-benchmark-admission.sh`, or a single suite via `bash scripts/pf.sh benchmark admission ...`.

Invalid cases should set `expect_failure_codes` to PCS reason codes (e.g. `PCS_CERTIFICATE_REJECTED`) or release-chain check IDs (e.g. `signed_input_bundle_hash_match`) depending on `verify_mode`.
