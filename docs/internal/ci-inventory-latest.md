# CI workflow inventory (auto-generated)

Generated: 2026-07-22T14:49:40Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

**Inventory honesty:** gated = last main-branch run must be `success`.
Path-filtered and schedule-only workflows are **not** required to run on every tip push.

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Inventory-gated (push/schedule) | 70 |
| Always-push (no path filter) | 3 |
| Path-push / schedule / mixed | 67 |
| Green (last run success) | 70 |
| Red (failure/cancelled/in progress) | 0 |
| No run / unknown | 17 |

## Workflows

| Workflow | Triggers | Gate kind | Last status | Gated | URL |
|----------|----------|-----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142408 |
| `adapters-ci.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29477314927 |
| `allowlist-sync.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29632293487 |
| `art-benchmark.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29731048931 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893563823 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29903805539 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29675263521 |
| `bench-swebench-unit.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142435 |
| `billing-test.yaml` | push, pull_request, schedule | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893749548 |
| `bundle-check.yaml` | pull_request | - | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247789 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279849 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893408947 |
| `ci.yml` | push, pull_request, workflow_dispatch | always-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060912 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29901132449 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29731446980 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | - | success | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29620729102 |
| `codeql.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29807083443 |
| `compliance.yaml` | release, workflow_dispatch | - | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404745 |
| `dependency-review.yml` | pull_request | - | no_run | no | - |
| `dep-graph.yaml` | pull_request | - | no_run | no | - |
| `dfa.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060836 |
| `docs-deploy.yaml` | push | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060911 |
| `dr-cross.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29738993817 |
| `edge-load.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29732965787 |
| `egress.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279890 |
| `engineering-budget-smoke.yml` | schedule, workflow_dispatch | schedule | **no_run** | yes | - |
| `evidence.yaml` | push, schedule, workflow_dispatch | mixed | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893600678 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404721 |
| `fuzz.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973816 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | - | no_run | no | - |
| `integration.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142448 |
| `jwks-validate.yml` | push, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29632293494 |
| `lean-offline.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29727800841 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29632293499 |
| `loadtest.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29734668561 |
| `morph-replay.yml` | push, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279955 |
| `multiarch-build.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060856 |
| `nightly-replay.yml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893240551 |
| `opa-test.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277608 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893261252 |
| `paper-conformance.yaml` | push, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893056261 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29477314965 |
| `perf.yaml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893685817 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29513118372 |
| `perf-proofmeter.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29734915457 |
| `pf-ci.yaml` | workflow_dispatch, workflow_call | - | success | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29620728032 |
| `pf-core-schema-check.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060838 |
| `pf-cross-repo-consumer.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29620719836 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29896531422 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29892374509 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142417 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29895021336 |
| `policy-build.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162 |
| `policy-gates.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29632293506 |
| `policy-pr-proof.yml` | pull_request | - | no_run | no | - |
| `pr-comments.yml` | pull_request | - | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29674793451 |
| `proof-bot.yaml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893207688 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29893271131 |
| `proto-compat.yaml` | push, pull_request, schedule | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29892226416 |
| `publish-updates.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29736775050 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | - | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29673173513 |
| `release.yaml` | push, workflow_dispatch | always-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29528283470 |
| `release-sbom.yml` | release | - | no_run | no | - |
| `replay.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279862 |
| `retrieval-gateway.yml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588 |
| `reusable-ci-extended.yml` | workflow_call | - | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | - | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | - | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | - | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | - | no_run | no | - |
| `revocation-sync.yaml` | push, pull_request, schedule, workflow_dispatch | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29738697621 |
| `sbom-diff.yaml` | push, pull_request, release | always-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29665060864 |
| `scorecards.yml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29725144744 |
| `slo-gates.yaml` | push, pull_request, schedule | mixed-path | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29892278257 |
| `spec-ai.yaml` | pull_request | - | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404740 |
| `test-windows.yml` | push, pull_request, workflow_dispatch | path-push | **no_run** | yes | - |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29675193589 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525078691 |
| `wasm-scan.yaml` | push, pull_request | path-push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389729 |

## Inventory-gated workflows not green

- `engineering-budget-smoke.yml (no_run) [schedule]`
- `test-windows.yml (no_run) [path-push]`

