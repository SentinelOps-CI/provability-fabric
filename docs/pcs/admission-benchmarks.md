# Admission benchmarks

Provability Fabric exposes a **release admission benchmark** that measures whether the admission controller correctly admits valid releases, rejects invalid ones, localizes failures, and produces useful explain output.

## Benchmark suites

Cases live under `benchmarks/admission/`.

| Workflow | Directory | Admission profile |
|----------|-----------|-------------------|
| LabTrust QC release | `labtrust_qc_release/` | `labtrust_qc_release` |
| Formal trust kernel | `formal_trust_kernel/` | `labtrust_qc_release` (formal-focused invalid cases) |
| Agent tool-use safety | `tool_use_safety/` | `agent_tool_use_safety` |
| Scientific computation | `computation_reproducibility/` | `scientific_computation_reproducibility` |

Each workflow includes `workflow.json`, `valid/` cases that must admit, and `invalid/` cases that must reject with expected codes.

Regenerate case JSON with the materialize script.

```bash
python scripts/materialize-admission-benchmark-cases.py
```

## Run benchmarks

For a single suite, run the following from the repository root.

```bash
bash scripts/pf.sh benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry ../pcs-core/examples/artifact_registry.valid.json \
  --out benchmark_runs/labtrust_admission \
  --validate \
  --validate-pcs-core-output ../pcs-core \
  --json-summary
```

All suites, matching CI, run through `make test-pcs-benchmark` or `bash scripts/pcs-benchmark-admission.sh`.

The LabTrust ingest producer gate runs with `make pcs-bench-producer`.

## Outputs

Each run writes a benchmark bundle under `--out`.

| Path | Role |
|------|------|
| `benchmark_report.v0.json` | Suite aggregate |
| `benchmark_run.v0.json` | Per-case runs |
| `failure_localization/` | Per invalid-case localization |
| `explain_quality/` | Per invalid-case explain scoring |
| `coverage/` | Registry, formal, profile, reproducibility coverage |
| `pcs_bench_ingest.v0.json` | Single-file import manifest for downstream benchmark tools |
| `commands.json` | Command log for reproducibility |

Add `--json-summary` for a compact stdout summary with `producer_id`, `suite_id`, `workflow_id`, metrics, and ingest path.

Downstream tools should read **`pcs_bench_ingest.v0.json`** as the primary import artifact.

## Validate a benchmark bundle

```bash
make validate-pcs-benchmark-bundle
bash scripts/pcs-validate-benchmark-bundle.sh benchmark_runs/labtrust_admission
```

Release-grade ingest validation uses the ingest validator script.

```bash
bash scripts/pcs-bench-validate-ingest.sh \
  --input benchmark_runs/labtrust_admission/pcs_bench_ingest.v0.json \
  --bundle-dir benchmark_runs/labtrust_admission \
  --pcs-core ../pcs-core \
  --release-grade
```

After changing emit logic, refresh the committed reference ingest.

```bash
make pcs-bench-producer
make export-pcs-benchmark-ingest-reference
make validate-pcs-reference-ingest
```

The reference artifact is `benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json`.

## Quality thresholds

CI and tests enforce the following expectations.

- LabTrust suites pass all cases with valid admission rate 1.0 and invalid rejection rate 1.0
- Tool-use and computation suites reach invalid rejection rate at least 0.80
- Explain quality score stays at or above 0.8 when required for a case

## Adding cases

1. Add fixtures under `tests/pcs/fixtures/`.
2. Register the case in `scripts/materialize-admission-benchmark-cases.py`.
3. Run `python scripts/materialize-admission-benchmark-cases.py`.
4. Run `make test-pcs-benchmark`.

Invalid cases should set `expect_failure_codes` to verification reason codes or release-chain check IDs depending on `verify_mode`.
