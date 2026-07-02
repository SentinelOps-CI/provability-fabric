# Criterion Baseline (F23)

Status: **workflow ready** — `workflow_dispatch` input `refresh_baseline` is wired in
`.github/workflows/bench-nightly-criterion.yaml`. Measured baseline refresh is pending the
first green `save-baseline` run on Linux CI.

The nightly `Bench Nightly Criterion` workflow compares against a Criterion baseline named `main`
under `target/criterion/`. Until a baseline is saved from a green main run, scheduled compare jobs
seed a baseline on first cache miss (see `compare-baseline` job).

## Refresh locally (Linux/WSL)

```bash
make bench-save-baseline
```

This runs `cargo bench -p provability-fabric-bench -- --save-baseline main` and updates this file
with date (UTC), git SHA, and machine metadata.

## Refresh via CI

1. Merge Wave 1 workflow fixes to `main`.
2. In GitHub Actions, run **Bench Nightly Criterion** with `workflow_dispatch` and set
   `refresh_baseline: true` (boolean input). A push to `main` under `bench/**` also triggers
   the `save-baseline` job.
3. Record the green run SHA and date below after the first successful refresh.
4. Confirm the next scheduled compare job passes.

| Field | Value |
|-------|-------|
| Last refresh SHA | _pending first CI run_ |
| Last refresh date (UTC) | _pending_ |
| Workflow | `bench-nightly-criterion.yaml` (`refresh_baseline: true`) |

## Thresholds

See [bench/README.md](README.md) — regression gates use Criterion defaults until measured baselines
are recorded here with date and machine.
