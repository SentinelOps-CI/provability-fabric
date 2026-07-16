# Criterion Baseline (F23)

Status: **DONE** — baseline refreshed on Linux CI (`save-baseline` green ×3 on `main` @
`1ab0d2d5`, including push + two `refresh_baseline=true` dispatches).

The nightly `Bench Nightly Criterion` workflow compares against a Criterion baseline named `main`
under `target/criterion/` (Actions cache key `criterion-main-*`). Scheduled compare jobs seed a
baseline on first cache miss (see `compare-baseline` job).

CI passes Criterion CLI overrides (`--sample-size 50 --measurement-time 5 --noplot`) so jobs stay
inside the Actions timeout budget; local `make bench-save-baseline` still uses the full group
settings in `bench/performance_benchmarks.rs`.

## Refresh locally (Linux/WSL)

```bash
make bench-save-baseline
```

This runs `cargo bench -p provability-fabric-bench -- --save-baseline main` and updates this file
with date (UTC), git SHA, and machine metadata.

## Refresh via CI

1. In GitHub Actions, run **Bench Nightly Criterion** with `workflow_dispatch` and set
   `refresh_baseline: true` (boolean input). A push to `main` under `bench/**` also triggers
   the `save-baseline` job.
2. Record the green run SHA and date below after a successful refresh.
3. Confirm a subsequent scheduled (or non-refresh dispatch) compare job passes.

| Field | Value |
|-------|-------|
| Last refresh SHA | `1ab0d2d53ca09d97bc4bab2b013fef25b668d7c4` |
| Last refresh date (UTC) | 2026-07-16T15:25:40Z |
| Last refresh machine | Linux 6.17.0-1018-azure x86_64 (GitHub Actions ubuntu-latest) |
| Workflow | `bench-nightly-criterion.yaml` (`refresh_baseline: true`) |
| Proof runs | [29508973817](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973817) (push), [29509027731](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509027731) (dispatch), [29509041247](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509041247) (dispatch) |

## Thresholds

See [bench/README.md](README.md) — regression gates use Criterion defaults until measured baselines
are recorded here with date and machine.
