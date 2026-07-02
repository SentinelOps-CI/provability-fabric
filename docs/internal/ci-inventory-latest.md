# CI workflow inventory (auto-generated)

Generated: 2026-07-02T12:47:01Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 86 |
| Gated (push/schedule on main) | 68 |
| Green (last run success) | 26 |
| Red (failure/cancelled/in progress) | 42 |
| No run / unknown | 18 |

## Workflows

| Workflow | Triggers | Last status | Gated | URL |
|----------|----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706332 |
| `adapters-ci.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705475 |
| `allowlist-sync.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271 |
| `art-benchmark.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585900934 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705704 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314414940 |
| `bench-swebench-unit.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576 |
| `billing-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399598636 |
| `bundle-check.yaml` | pull_request | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705316 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705523 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568878282 |
| `ci.yml` | push, pull_request, workflow_dispatch | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705582 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576040030 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28367886347 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318 |
| `codeql.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705418 |
| `compliance.yaml` | release, workflow_dispatch | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705589 |
| `dependency-review.yml` | pull_request | no_run | no | - |
| `dep-graph.yaml` | pull_request | no_run | no | - |
| `dfa.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705338 |
| `docs-deploy.yaml` | push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705536 |
| `dr-cross.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313345565 |
| `edge-load.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429 |
| `egress.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705538 |
| `evidence.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569079948 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705539 |
| `fuzz.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705323 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `incident-e2e.yaml` | workflow_dispatch | no_run | no | - |
| `incident-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108 |
| `integration.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085 |
| `jwks-validate.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705506 |
| `lean-offline.yaml` | push, schedule, workflow_dispatch | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705320 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706852 |
| `loadtest.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626 |
| `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631 |
| `morph-replay.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516 |
| `multiarch-build.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705304 |
| `nightly-replay.yml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568693881 |
| `opa-test.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399591865 |
| `paper-conformance.yaml` | push, schedule, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705694 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705524 |
| `perf.yaml` | schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569153198 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705629 |
| `perf-proofmeter.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889 |
| `pf-ci.yaml` | workflow_call | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943 |
| `pf-cross-repo-consumer.yaml` | pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28572843688 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706202 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297 |
| `policy-build.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162 |
| `policy-gates.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585707156 |
| `policy-pr-proof.yml` | pull_request | no_run | no | - |
| `pr-comments.yml` | pull_request | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705511 |
| `proof-bot.yaml` | schedule, workflow_dispatch, issue_comment | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28589794992 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882 |
| `proto-compat.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706169 |
| `publish-updates.yaml` | push, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28312328896 |
| `release.yaml` | push, workflow_dispatch | **no_run** | yes | - |
| `release-sbom.yml` | release | no_run | no | - |
| `replay.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517 |
| `retrieval-gateway.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706166 |
| `reusable-ci-extended.yml` | workflow_call | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | no_run | no | - |
| `revocation-sync.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470 |
| `sbom-diff.yaml` | push, pull_request, release | **queued** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705575 |
| `scorecards.yml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706992 |
| `slo-gates.yaml` | push, pull_request, schedule | **skipped** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647128 |
| `spec-ai.yaml` | pull_request | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705309 |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314313517 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | **no_run** | yes | - |
| `wasm-scan.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705335 |

## Gated workflows not green

- `adapters-ci.yml (failure)`
- `art-benchmark.yaml (failure)`
- `bench-nightly-criterion.yaml (in_progress)`
- `bench-swebench-stress-scheduled.yaml (failure)`
- `bench-swebench-unit.yaml (failure)`
- `billing-test.yaml (failure)`
- `ci.yml (in_progress)`
- `codeql.yaml (failure)`
- `demo-e2e.yml (failure)`
- `dr-cross.yaml (failure)`
- `edge-load.yaml (failure)`
- `egress.yml (failure)`
- `evidence-v01-smoke.yml (queued)`
- `incident-test.yaml (failure)`
- `integration.yaml (failure)`
- `lean-offline.yaml (in_progress)`
- `loadtest.yaml (failure)`
- `marketplace-e2e.yaml (queued)`
- `multiarch-build.yaml (failure)`
- `nightly-replay.yml (failure)`
- `opa-test.yaml (failure)`
- `operational-excellence.yaml (failure)`
- `paper-conformance.yaml (queued)`
- `pcs-ci.yml (failure)`
- `perf.yaml (cancelled)`
- `performance-gate.yaml (queued)`
- `perf-proofmeter.yaml (failure)`
- `pf-cross-repo-consumer.yaml (failure)`
- `pf-reusable-caller.yaml (failure)`
- `policy-gates.yaml (failure)`
- `proof-bot.yaml (queued)`
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
- `wasm-scan.yaml (failure)`

