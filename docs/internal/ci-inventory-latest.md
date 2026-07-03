# CI workflow inventory (auto-generated)

Generated: 2026-07-03T01:04:23Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on main) | 69 |
| Green (last run success) | 31 |
| Red (failure/cancelled/in progress) | 38 |
| No run / unknown | 18 |

## Workflows

| Workflow | Triggers | Last status | Gated | URL |
|----------|----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247814 |
| `adapters-ci.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922311 |
| `allowlist-sync.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271 |
| `art-benchmark.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247839 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705704 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314414940 |
| `bench-swebench-unit.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576 |
| `billing-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922315 |
| `bundle-check.yaml` | pull_request | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247789 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116959 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568878282 |
| `ci.yml` | push, pull_request, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260538 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576040030 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28367886347 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318 |
| `codeql.yaml` | push, pull_request, schedule | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260402 |
| `compliance.yaml` | release, workflow_dispatch | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705589 |
| `dependency-review.yml` | pull_request | no_run | no | - |
| `dep-graph.yaml` | pull_request | no_run | no | - |
| `dfa.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247813 |
| `docs-deploy.yaml` | push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247796 |
| `dr-cross.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313345565 |
| `edge-load.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429 |
| `egress.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705538 |
| `evidence.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569079948 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28630303030 |
| `fuzz.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247797 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `incident-e2e.yaml` | workflow_dispatch | no_run | no | - |
| `incident-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108 |
| `integration.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247795 |
| `jwks-validate.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922346 |
| `lean-offline.yaml` | push, schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922294 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922304 |
| `loadtest.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626 |
| `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631 |
| `morph-replay.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516 |
| `multiarch-build.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260395 |
| `nightly-replay.yml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568693881 |
| `opa-test.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260382 |
| `paper-conformance.yaml` | push, schedule, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247809 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28630303009 |
| `perf.yaml` | schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569153198 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705629 |
| `perf-proofmeter.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889 |
| `pf-ci.yaml` | workflow_call | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943 |
| `pf-core-schema-check.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260388 |
| `pf-cross-repo-consumer.yaml` | pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28572843688 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922281 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297 |
| `policy-build.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162 |
| `policy-gates.yaml` | push, pull_request | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247811 |
| `policy-pr-proof.yml` | pull_request | no_run | no | - |
| `pr-comments.yml` | pull_request | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247817 |
| `proof-bot.yaml` | schedule, workflow_dispatch, issue_comment | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28589794992 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882 |
| `proto-compat.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706169 |
| `publish-updates.yaml` | push, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28312328896 |
| `release.yaml` | push, workflow_dispatch | **no_run** | yes | - |
| `release-sbom.yml` | release | no_run | no | - |
| `replay.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517 |
| `retrieval-gateway.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922316 |
| `reusable-ci-extended.yml` | workflow_call | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | no_run | no | - |
| `revocation-sync.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470 |
| `sbom-diff.yaml` | push, pull_request, release | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260398 |
| `scorecards.yml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631260383 |
| `slo-gates.yaml` | push, pull_request, schedule | **skipped** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647128 |
| `spec-ai.yaml` | pull_request | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116949 |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314313517 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | **no_run** | yes | - |
| `wasm-scan.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922329 |

## Gated workflows not green

- `adapters-ci.yml (failure)`
- `art-benchmark.yaml (failure)`
- `bench-nightly-criterion.yaml (in_progress)`
- `bench-swebench-stress-scheduled.yaml (failure)`
- `bench-swebench-unit.yaml (failure)`
- `billing-test.yaml (failure)`
- `ci.yml (queued)`
- `codeql.yaml (in_progress)`
- `demo-e2e.yml (failure)`
- `dr-cross.yaml (failure)`
- `edge-load.yaml (failure)`
- `egress.yml (failure)`
- `incident-test.yaml (failure)`
- `integration.yaml (failure)`
- `lean-offline.yaml (cancelled)`
- `loadtest.yaml (failure)`
- `multiarch-build.yaml (failure)`
- `nightly-replay.yml (failure)`
- `opa-test.yaml (failure)`
- `operational-excellence.yaml (queued)`
- `paper-conformance.yaml (queued)`
- `pcs-ci.yml (failure)`
- `perf.yaml (cancelled)`
- `perf-proofmeter.yaml (failure)`
- `pf-cross-repo-consumer.yaml (failure)`
- `pf-reusable-caller.yaml (failure)`
- `policy-gates.yaml (queued)`
- `proof-bot.yaml (failure)`
- `proof-fuzz.yaml (failure)`
- `proto-compat.yaml (failure)`
- `publish-updates.yaml (failure)`
- `redteam.yaml (failure)`
- `release.yaml (no_run)`
- `revocation-sync.yaml (failure)`
- `sbom-diff.yaml (queued)`
- `slo-gates.yaml (skipped)`
- `trust-fire-ga-test.yaml (failure)`
- `verify-publish-bundle.yaml (no_run)`

