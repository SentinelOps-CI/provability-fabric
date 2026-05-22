# PCS release checklist

Run before tagging a Provability Fabric PCS release. CI on `main` runs the same gates via [.github/workflows/pcs-ci.yml](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/pcs-ci.yml).

## Prerequisites

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
export PCS_CORE_PATH=../pcs-core
```

## One-command gate (recommended)

Linux / Git Bash:

```bash
make pcs-release-gate
```

Windows (PowerShell):

```powershell
$env:PCS_CORE_PATH = "..\pcs-core"
powershell -File scripts/pcs-release-gate.ps1
```

This runs schema sync check, `test-pcs-full`, demos, and the PF clean-chain segment.

## Step-by-step (same as CI)

```bash
make validate-pcs-schema-diff    # or: make sync-pcs-schemas if pcs-core updated
make test-pcs-full
make demo-pcs
make demo-pcs-release
make pcs-v01-pf-chain
```

Optional cross-repo chain (requires LabTrust-Gym, CertifyEdge, Scientific Memory):

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
- `benchmarks/admission/examples/*.pcs_bench_ingest.reference.json` (if producer output changed)
- Code and documentation under `docs/pcs/`

Do **not** commit `benchmark_runs/`, `release-run/` working outputs, or `_ci_sim_pcs/`.
