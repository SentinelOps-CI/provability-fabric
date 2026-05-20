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

Single workflow:

```bash
pf benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry ../pcs-core/examples/artifact_registry.valid.json \
  --out benchmark_runs/labtrust_admission \
  --json-summary
```

All workflows (CI / local gate):

```bash
bash scripts/pcs-benchmark-admission.sh
```

Or via Make:

```bash
make test-pcs-benchmark
```

On Windows (Git Bash without `go` on PATH), the shell script builds `core/cli/pf/pf.exe` automatically. You can also run:

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
| `commands.json` | — | Command log for reproducibility |
| `logs/run.log` | — | Case outcome log |
| `runs/<case_id>/` | — | Per-case copies of run / explain / FLR artifacts |
| `admission_benchmark_suite.v0.json` | PF-internal | Suite metrics + case outcomes (legacy PF summary) |

Use `--json-summary` to print a compact JSON summary (metrics + pass/fail counts) on stdout.

### Metrics (`admission_benchmark_suite.v0.json` → `metrics`)

| Metric | Meaning |
|--------|---------|
| `valid_release_admission_rate` | Share of `valid/` cases that admitted |
| `invalid_release_rejection_rate` | Share of `invalid/` cases that rejected with matching codes |
| `failure_localization_accuracy` | Share of localized invalid cases where the failed RCVR check matches `localization.check_id` |
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

For invalid cases with `explain_requirements`, PF emits pcs-core `ExplainQualityReport.v0` per case, scoring explain sections (`verification`, `hashes`, `handoffs`, `formal_checks`, `repair_hints`, etc.) mapped from failure code, artifact path, expected/actual values, responsible component, repair hints, and optional registry/handoff/formal references.

Formal trust-kernel enforcement (proof obligations, Lean checks, theorem references) is exercised primarily in the **LabTrust QC release** workflow invalid cases (`missing_proof_obligation`, `failed_lean_check`, etc.).

## pcs-bench integration

Downstream **pcs-bench** should ingest `benchmark_report.v0.json` plus the root `*.v0.json` arrays and `runs/` tree. Schemas are synced from pcs-core into `config/schemas/pcs/` and embedded in `adapters/pcs/schemas/`.

Validate a bundle directory in Go tests or tooling:

```go
pcs.ValidateAdmissionBenchmarkBundleDir(repoRoot, bundleDir)
```

Canonical required invalid case IDs (union across workflows) are listed in `pcs.RequiredAdmissionInvalidCaseIDs` (`admission_benchmark_bundle.go`).

Minimum gate thresholds (current PF tests):

- LabTrust: invalid rejection rate ≥ 0.85, valid admission rate = 1.0
- Tool-use / computation: invalid rejection rate ≥ 0.80

## Adding cases

1. Add or extend fixtures under `tests/pcs/fixtures/`.
2. Add a case entry in `scripts/materialize-admission-benchmark-cases.py`.
3. Run `python scripts/materialize-admission-benchmark-cases.py`.
4. Run `make test-pcs-benchmark` or the single-suite `pf benchmark admission` command.

Invalid cases should set `expect_failure_codes` to PCS reason codes (e.g. `PCS_CERTIFICATE_REJECTED`) or release-chain check IDs (e.g. `signed_input_bundle_hash_match`) depending on `verify_mode`.
