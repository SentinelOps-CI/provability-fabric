# PCS release checklist

Complete these steps before tagging a Provability Fabric PCS release. CI on `main` runs the same gates defined in [.github/workflows/pcs-ci.yml](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/pcs-ci.yml).

## Prerequisites

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
export PCS_CORE_PATH=../pcs-core
```

## One-command gate (recommended)

On Linux or Git Bash, run the following.

```bash
make pcs-release-gate
```

On Windows with PowerShell, run the following.

```powershell
$env:PCS_CORE_PATH = "..\pcs-core"
powershell -File scripts/pcs-release-gate.ps1
```

This target runs the schema sync check, `test-pcs-full`, demos, and the PF clean-chain segment.

## Step-by-step (same as CI)

```bash
make validate-pcs-schema-diff    # or make sync-pcs-schemas if pcs-core updated
make test-pcs-full
make demo-pcs
make demo-pcs-release
make pcs-v01-pf-chain
```

The optional cross-repo chain requires LabTrust-Gym, CertifyEdge, and Scientific Memory.

```bash
export PCS_DETERMINISTIC=1
make pcs-v01-clean-chain
```

## After changing benchmark emit logic

```bash
make pcs-bench-producer
make export-pcs-benchmark-ingest-reference
make validate-pcs-reference-ingest
```

## Fixture refresh

| Goal | Command |
|------|---------|
| Sync labtrust release from pcs-core | `make sync-pcs-rc-fixtures` |
| Sync computation release | `make sync-pcs-computation-fixtures` |
| Full chain freeze | `make freeze-pcs-labtrust-release` |

See [Fixtures](fixtures.md).

## What must be committed

- `config/schemas/pcs/` and `adapters/pcs/schemas/` (in sync with pcs-core)
- `tests/pcs/fixtures/` release evidence (atomic updates only)
- `benchmarks/admission/examples/*.pcs_bench_ingest.reference.json` (when producer output changed)
- Code and documentation under `docs/pcs/`

Keep `benchmark_runs/`, `release-run/` working outputs, and `_ci_sim_pcs/` out of version control.
