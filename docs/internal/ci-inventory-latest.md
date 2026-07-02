# CI workflow inventory (auto-generated)

Generated: 2026-07-02T08:20:38Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 86 |
| Gated (push/schedule on main) | 68 |
| Green (last run success) | 13 |
| Red (failure/cancelled/in progress) | 53 |
| No run / unknown | 20 |

## Workflows

| Workflow | Triggers | Last status | Gated | URL |
|----------|----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27676760872 |
| `adapters-ci.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576589 |
| `allowlist-sync.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576585 |
| `art-benchmark.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569060330 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28508331042 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314414940 |
| `bench-swebench-unit.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576 |
| `billing-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399598636 |
| `bundle-check.yaml` | pull_request | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576613 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27670516758 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568878282 |
| `ci.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677074379 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28505615641 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28367886347 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318 |
| `codeql.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28429083030 |
| `compliance.yaml` | release, workflow_dispatch | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597109278 |
| `dependency-review.yml` | pull_request | no_run | no | - |
| `dep-graph.yaml` | pull_request | no_run | no | - |
| `dfa.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576566 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677074296 |
| `docs-deploy.yaml` | push | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677074241 |
| `dr-cross.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313345565 |
| `edge-load.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429 |
| `egress.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512638971 |
| `evidence.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569079948 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27686356513 |
| `fuzz.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27509871701 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `incident-e2e.yaml` | workflow_dispatch | no_run | no | - |
| `incident-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108 |
| `integration.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27676760223 |
| `jwks-validate.yml` | push, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17535475445 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597316373 |
| `lean-offline.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576601 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576592 |
| `loadtest.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626 |
| `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17508000336 |
| `morph-replay.yml` | push, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597316360 |
| `multiarch-build.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677074328 |
| `nightly-replay.yml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568693881 |
| `opa-test.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399591865 |
| `paper-conformance.yaml` | push, pull_request, schedule | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568545852 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576571 |
| `perf.yaml` | schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569153198 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27676760071 |
| `perf-proofmeter.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889 |
| `pf-ci.yaml` | workflow_call | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943 |
| `pf-cross-repo-consumer.yaml` | pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28572843688 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568431511 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597172922 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28570861483 |
| `policy-build.yml` | push, pull_request | **no_run** | yes | - |
| `policy-gates.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576560 |
| `policy-pr-proof.yml` | pull_request | no_run | no | - |
| `pr-comments.yml` | pull_request | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313655953 |
| `proof-bot.yaml` | schedule, workflow_dispatch, issue_comment | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399500362 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882 |
| `proto-compat.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568320371 |
| `publish-updates.yaml` | push, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28312328896 |
| `release.yaml` | push, workflow_dispatch | **no_run** | yes | - |
| `release-sbom.yml` | release | no_run | no | - |
| `replay.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27510612216 |
| `retrieval-gateway.yml` | push, pull_request | **no_run** | yes | - |
| `reusable-ci-extended.yml` | workflow_call | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | no_run | no | - |
| `revocation-sync.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470 |
| `sbom-diff.yaml` | push, pull_request, release | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677074405 |
| `scorecards.yml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28361288280 |
| `slo-gates.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568369544 |
| `spec-ai.yaml` | pull_request | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27670516732 |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314313517 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | **no_run** | yes | - |
| `wasm-scan.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17750206124 |

## Gated workflows not green

- `adapters-ci.yml (failure)`
- `allowlist-sync.yaml (failure)`
- `art-benchmark.yaml (failure)`
- `bench-nightly-criterion.yaml (failure)`
- `bench-swebench-stress-scheduled.yaml (failure)`
- `bench-swebench-unit.yaml (failure)`
- `billing-test.yaml (failure)`
- `cargo-deny.yml (failure)`
- `codeql.yaml (failure)`
- `demo-e2e.yml (failure)`
- `dfa.yaml (failure)`
- `docs-build.yaml (failure)`
- `docs-deploy.yaml (failure)`
- `dr-cross.yaml (failure)`
- `edge-load.yaml (failure)`
- `egress.yml (failure)`
- `fuzz.yaml (failure)`
- `incident-test.yaml (failure)`
- `integration.yaml (failure)`
- `jwks-validate.yml (failure)`
- `lean-morph.yml (failure)`
- `lean-offline.yaml (failure)`
- `lean-style.yaml (failure)`
- `loadtest.yaml (failure)`
- `marketplace-e2e.yaml (failure)`
- `morph-replay.yml (failure)`
- `multiarch-build.yaml (failure)`
- `nightly-replay.yml (failure)`
- `opa-test.yaml (failure)`
- `operational-excellence.yaml (failure)`
- `paper-conformance.yaml (in_progress)`
- `pcs-ci.yml (failure)`
- `perf.yaml (cancelled)`
- `performance-gate.yaml (failure)`
- `perf-proofmeter.yaml (failure)`
- `pf-cross-repo-consumer.yaml (failure)`
- `pf-reusable-caller.yaml (failure)`
- `platform-cert-validate.yml (failure)`
- `platform-perf-smoke.yml (failure)`
- `platform-replay.yml (failure)`
- `policy-build.yml (no_run)`
- `policy-gates.yaml (failure)`
- `privacy-test.yaml (failure)`
- `proof-fuzz.yaml (failure)`
- `publish-updates.yaml (failure)`
- `redteam.yaml (failure)`
- `release.yaml (no_run)`
- `replay.yml (failure)`
- `retrieval-gateway.yml (no_run)`
- `revocation-sync.yaml (failure)`
- `sbom-diff.yaml (failure)`
- `slo-gates.yaml (failure)`
- `trust-fire-ga-test.yaml (failure)`
- `verify-publish-bundle.yaml (no_run)`
- `wasm-scan.yaml (failure)`

