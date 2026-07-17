# CI workflow inventory (auto-generated)

Generated: 2026-07-17T22:44:44Z UTC
Repository: `SentinelOps-CI/provability-fabric` branch `main`

## Summary

| Metric | Count |
|--------|------:|
| Total workflow files | 87 |
| Gated (push/schedule on main) | 61 |
| Green (last run success) | 61 |
| Red (failure/cancelled/in progress) | 10 |
| No run / unknown | 16 |

## Workflows

| Workflow | Triggers | Last status | Gated | URL |
|----------|----------|-------------|-------|-----|
| `actionlint.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29615810135 |
| `adapters-ci.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29477314927 |
| `allowlist-sync.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271 |
| `art-benchmark.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401 |
| `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556889681 |
| `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29565200288 |
| `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522474048 |
| `bench-swebench-unit.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525017320 |
| `billing-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29557024660 |
| `bundle-check.yaml` | pull_request | no_run | no | - |
| `cargo-deny.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28631247789 |
| `cert-validate.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279849 |
| `chaos-nightly.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556748331 |
| `ci.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419795 |
| `ci-nightly-pytest.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29563146130 |
| `ci-weekly-full.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29515858240 |
| `cla-bot.yaml` | pull_request, workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318 |
| `codeql.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419648 |
| `compliance.yaml` | release, workflow_dispatch | no_run | no | - |
| `demo-e2e.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404745 |
| `dependency-review.yml` | pull_request | no_run | no | - |
| `dep-graph.yaml` | pull_request | no_run | no | - |
| `dfa.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153 |
| `docs-build.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419669 |
| `docs-deploy.yaml` | push | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419673 |
| `dr-cross.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29180887456 |
| `edge-load.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429 |
| `egress.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279890 |
| `evidence.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556910731 |
| `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404721 |
| `fuzz.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973816 |
| `heartbeat-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `incident-e2e.yaml` | workflow_dispatch | no_run | no | - |
| `incident-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556657458 |
| `integration.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757 |
| `jwks-validate.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444 |
| `lean-morph.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419681 |
| `lean-offline.yaml` | workflow_dispatch | cancelled | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29491617791 |
| `lean-style.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419642 |
| `loadtest.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626 |
| `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631 |
| `morph-replay.yml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279955 |
| `multiarch-build.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419613 |
| `nightly-replay.yml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556141894 |
| `opa-test.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277608 |
| `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419643 |
| `paper-conformance.yaml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556022920 |
| `pcs-ci.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29477314965 |
| `perf.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556980152 |
| `performance-gate.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29513118372 |
| `perf-proofmeter.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889 |
| `pf-ci.yaml` | workflow_call | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943 |
| `pf-core-schema-check.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419634 |
| `pf-cross-repo-consumer.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29615810099 |
| `pf-reusable-caller.yaml` | pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29559243589 |
| `platform-cert-validate.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29555866486 |
| `platform-perf-smoke.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549722 |
| `platform-replay.yml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29558106368 |
| `policy-build.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162 |
| `policy-gates.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973752 |
| `policy-pr-proof.yml` | pull_request | no_run | no | - |
| `pr-comments.yml` | pull_request | no_run | no | - |
| `privacy-test.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973818 |
| `proof-bot.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556105465 |
| `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29556158919 |
| `proto-compat.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29555744101 |
| `publish-updates.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888 |
| `rbac-test.yaml` | pull_request, workflow_dispatch | no_run | no | - |
| `redteam.yaml` | pull_request, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29520388261 |
| `release.yaml` | push, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29528283470 |
| `release-sbom.yml` | release | no_run | no | - |
| `replay.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29470279862 |
| `retrieval-gateway.yml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588 |
| `reusable-ci-extended.yml` | workflow_call | no_run | no | - |
| `reusable-ci-go-node.yml` | workflow_call | no_run | no | - |
| `reusable-ci-lean.yml` | workflow_call | no_run | no | - |
| `reusable-ci-prepare.yml` | workflow_call | no_run | no | - |
| `reusable-ci-rust.yml` | workflow_call | no_run | no | - |
| `revocation-sync.yaml` | workflow_dispatch | failure | no | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470 |
| `sbom-diff.yaml` | push, pull_request, release | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419638 |
| `scorecards.yml` | push, schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29616419640 |
| `slo-gates.yaml` | push, pull_request, schedule | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29555778731 |
| `spec-ai.yaml` | pull_request | no_run | no | - |
| `standards-pin.yml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29465404740 |
| `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522471801 |
| `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525078691 |
| `wasm-scan.yaml` | push, pull_request | success | yes | https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389729 |

