# Admission benchmarks

Provability Fabric exposes a **release admission benchmark** that measures whether it correctly admits valid releases, rejects invalid ones, localizes failures, and produces useful explain output.

## Benchmark suites

Cases live under `benchmarks/admission/`:

| Workflow | Directory | Admission profile |
|----------|-----------|-------------------|
| LabTrust QC release | `labtrust_qc_release/` | `labtrust_qc_release` |
| Formal trust kernel | `formal_trust_kernel/` | `labtrust_qc_release` (formal-focused invalid cases) |
| Agent tool-use safety | `tool_use_safety/` | `agent_tool_use_safety` |
| Scientific computation | `computation_reproducibility/` | `scientific_computation_reproducibility` |

Each workflow has `workflow.json`, `valid/` cases (must admit), and `invalid/` cases (must reject with expected codes).

Regenerate case JSON:

```bash
python scripts/materialize-admission-benchmark-cases.py
```

## Run benchmarks

Single suite:

```bash
bash scripts/pf.sh benchmark admission \
  --cases benchmarks/admission/labtrust_qc_release \
  --registry ../pcs-core/examples/artifact_registry.valid.json \
  --out benchmark_runs/labtrust_admission \
  --validate \
  --validate-pcs-core-output ../pcs-core \
  --json-summary
```

All suites (matches CI):

```bash
make test-pcs-benchmark
# or
bash scripts/pcs-benchmark-admission.sh
```

Producer gate (LabTrust ingest):

```bash
make pcs-bench-producer
```

## Outputs

Each run writes a benchmark bundle under `--out`:

| Path | Role |
|------|------|
| `benchmark_report.v0.json` | Suite aggregate |
| `benchmark_run.v0.json` | Per-case runs |
| `failure_localization/` | Per invalid-case localization |
| `explain_quality/` | Per invalid-case explain scoring |
| `coverage/` | Registry, formal, profile, reproducibility coverage |
| `pcs_bench_ingest.v0.json` | Single-file import manifest for downstream benchmark tools |
| `commands.json` | Command log for reproducibility |

Use `--json-summary` for a compact stdout summary (`producer_id`, `suite_id`, `workflow_id`, metrics, ingest path).

Downstream tools should read **`pcs_bench_ingest.v0.json`** as the primary import artifact.

## Validate a benchmark bundle

```bash
make validate-pcs-benchmark-bundle
bash scripts/pcs-validate-benchmark-bundle.sh benchmark_runs/labtrust_admission
```

Release-grade ingest validation:

```bash
bash scripts/pcs-bench-validate-ingest.sh \
  --input benchmark_runs/labtrust_admission/pcs_bench_ingest.v0.json \
  --bundle-dir benchmark_runs/labtrust_admission \
  --pcs-core ../pcs-core \
  --release-grade
```

Refresh the committed reference ingest after changing emit logic:

```bash
make pcs-bench-producer
make export-pcs-benchmark-ingest-reference
make validate-pcs-reference-ingest
```

Reference artifact: `benchmarks/admission/examples/labtrust_qc_release.pcs_bench_ingest.reference.json`.

## Quality thresholds

CI and tests enforce:

- LabTrust: all cases pass; valid admission rate = 1.0; invalid rejection rate = 1.0
- Tool-use and computation: invalid rejection rate ≥ 0.80
- Explain quality score ≥ 0.8 when required for a case

## Adding cases

1. Add fixtures under `tests/pcs/fixtures/`.
2. Register the case in `scripts/materialize-admission-benchmark-cases.py`.
3. Run `python scripts/materialize-admission-benchmark-cases.py`.
4. Run `make test-pcs-benchmark`.

Invalid cases should set `expect_failure_codes` to verification reason codes or release-chain check IDs depending on `verify_mode`.
