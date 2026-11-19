# PCS release checklist

Complete these steps before tagging a Provability Fabric PCS release. CI on `main` runs the same gates defined in [.github/workflows/pcs-ci.yml](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/pcs-ci.yml).

## Prerequisites

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
git -C ../pcs-core checkout 9db2ec210c2b5627a72b5cc23a10aebe88dd5012
export PCS_CORE_PATH=../pcs-core
```

The checked-in PCS schema mirrors target the `pcs-core` compatibility snapshot
`9db2ec210c2b5627a72b5cc23a10aebe88dd5012` (July 23, 2026). CI checks this exact immutable commit,
not the continuously changing upstream default branch. This pin preserves
the current consumer/fixture contract; it does not claim compatibility with
newer upstream schemas. A separate schema migration must evaluate all changed
definitions, referential constraints, generators, Go validators, and release
fixtures before upgrading the snapshot. Do not use `make sync-pcs-schemas`
against an unreviewed newer checkout: that command replaces schema copies.

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
make validate-pcs-schema-diff    # checks the pinned pcs-core compatibility snapshot
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

- `config/schemas/pcs/` and `adapters/pcs/schemas/` (identical checked-in mirrors, validated against pinned pcs-core)
- `tests/pcs/fixtures/` release evidence (atomic updates only)
- `benchmarks/admission/examples/*.pcs_bench_ingest.reference.json` (when producer output changed)
- Code and documentation under `docs/pcs/`

Keep `benchmark_runs/`, `release-run/` working outputs, and `_ci_sim_pcs/` out of version control.
