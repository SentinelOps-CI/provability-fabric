# Sidecar integration tests

## Active targets

These binaries are registered in `Cargo.toml` (`[[test]]` entries) and run in CI with:

`cargo test -p sidecar-watcher`

- `declassify_engine.rs`
- `integration_tests.rs`
- `break_glass_mechanism.rs`
- `dfa_equiv.rs` (includes `proptest` where enabled)

## Quarantined sources

The package sets `autotests = false`. The following files remain in this directory for future repair but are **not** built until their expectations match the current crate API:

- `events_plan_dsl.rs`
- `ni_monitor_egress.rs`
- `safety_case_bundle.rs`
- `hardened_adapters.rs`

To work on one, add a `[[test]]` entry and fix compile errors, or move it to a `tests_pending/` tree and reference it explicitly.
