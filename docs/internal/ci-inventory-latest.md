# CI workflow inventory (auto-generated)

Generated: 2026-07-15T19:33:11Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on main) | 69 |
| Green (last run success) | 39 |
| Red (failure/cancelled/in progress) | 30 |
| No run / unknown | 18 |

## Workflows

| Workflow | Triggers | Last status | Gated | URL |
|----------|----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338295 |
| `adapters-ci.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922311 |
| `allowlist-sync.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271 |
| `art-benchmark.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400233715 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29399443152 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29181697304 |
| `bench-swebench-unit.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576 |
| `billing-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29390196605 |
| `bundle-check.yaml` | pull_request | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247789 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116959 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389944563 |
| `ci.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338622 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29397125062 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29239884669 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318 |
| `codeql.yaml` | push, pull_request, schedule | **in_progress** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338299 |
| `compliance.yaml` | release, workflow_dispatch | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705589 |
| `dependency-review.yml` | pull_request | no_run | no | - |
| `dep-graph.yaml` | pull_request | no_run | no | - |
| `dfa.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400238049 |
| `docs-deploy.yaml` | push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400238330 |
| `dr-cross.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29180887456 |
| `edge-load.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429 |
| `egress.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705538 |
| `evidence.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29390099186 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28630303030 |
| `fuzz.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400234167 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `incident-e2e.yaml` | workflow_dispatch | no_run | no | - |
| `incident-test.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389873758 |
| `integration.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389617 |
| `jwks-validate.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922346 |
| `lean-offline.yaml` | push, schedule, workflow_dispatch | **cancelled** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29391379051 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922304 |
| `loadtest.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626 |
| `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631 |
| `morph-replay.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516 |
| `multiarch-build.yaml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338384 |
| `nightly-replay.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389783725 |
| `opa-test.yaml` | push, pull_request | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338305 |
| `paper-conformance.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28630303009 |
| `perf.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29390157047 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705629 |
| `perf-proofmeter.yaml` | push, pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889 |
| `pf-ci.yaml` | workflow_call | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943 |
| `pf-core-schema-check.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338364 |
| `pf-cross-repo-consumer.yaml` | pull_request, schedule | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29393328663 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389451594 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549722 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29391814477 |
| `policy-build.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162 |
| `policy-gates.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400234277 |
| `policy-pr-proof.yml` | pull_request | no_run | no | - |
| `pr-comments.yml` | pull_request | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29400234105 |
| `proof-bot.yaml` | schedule, workflow_dispatch, issue_comment | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441339172 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389829657 |
| `proto-compat.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389325187 |
| `publish-updates.yaml` | push, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29179664746 |
| `release.yaml` | push, workflow_dispatch | **no_run** | yes | - |
| `release-sbom.yml` | release | no_run | no | - |
| `replay.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517 |
| `retrieval-gateway.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588 |
| `reusable-ci-extended.yml` | workflow_call | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | no_run | no | - |
| `revocation-sync.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470 |
| `sbom-diff.yaml` | push, pull_request, release | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338256 |
| `scorecards.yml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338415 |
| `slo-gates.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389917 |
| `spec-ai.yaml` | pull_request | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116949 |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | **failure** | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29181636975 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | **no_run** | yes | - |
| `wasm-scan.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389729 |

## Gated workflows not green

- `adapters-ci.yml (failure)`
- `art-benchmark.yaml (failure)`
- `bench-nightly-criterion.yaml (cancelled)`
- `bench-swebench-stress-scheduled.yaml (failure)`
- `bench-swebench-unit.yaml (failure)`
- `billing-test.yaml (failure)`
- `ci-weekly-full.yml (failure)`
- `codeql.yaml (in_progress)`
- `demo-e2e.yml (failure)`
- `dr-cross.yaml (failure)`
- `edge-load.yaml (failure)`
- `egress.yml (failure)`
- `incident-test.yaml (failure)`
- `lean-offline.yaml (cancelled)`
- `loadtest.yaml (failure)`
- `multiarch-build.yaml (failure)`
- `opa-test.yaml (failure)`
- `operational-excellence.yaml (failure)`
- `pcs-ci.yml (failure)`
- `perf.yaml (failure)`
- `perf-proofmeter.yaml (failure)`
- `pf-cross-repo-consumer.yaml (failure)`
- `proof-bot.yaml (failure)`
- `proof-fuzz.yaml (failure)`
- `publish-updates.yaml (failure)`
- `redteam.yaml (failure)`
- `release.yaml (no_run)`
- `revocation-sync.yaml (failure)`
- `trust-fire-ga-test.yaml (failure)`
- `verify-publish-bundle.yaml (no_run)`

