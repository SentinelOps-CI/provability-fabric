CI workflow inventory - repo=SentinelOps-CI/provability-fabric branch=main
WORKFLOW                                   TRIGGERS                     STATUS       URL
--------------------------------------------------------------------------------------------------------------
actionlint.yml                             push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706332
adapters-ci.yml                            push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705475
allowlist-sync.yaml                        push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271
art-benchmark.yaml                         push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401
bench-nightly-criterion.yaml               push, pull_request, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585900934
bench-swebench-smoke.yaml                  push, pull_request, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705704
bench-swebench-stress-scheduled.yaml       schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314414940
bench-swebench-unit.yaml                   push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576
billing-test.yaml                          push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399598636
bundle-check.yaml                          pull_request                 no_run       -
cargo-deny.yml                             push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705316
cert-validate.yml                          push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705523
chaos-nightly.yaml                         schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568878282
ci.yml                                     push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705582
ci-nightly-pytest.yml                      schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576040030
ci-weekly-full.yml                         schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28367886347
cla-bot.yaml                               pull_request, workflow_dispatch failure      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318
codeql.yaml                                push, pull_request, schedule queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705418
compliance.yaml                            release, workflow_dispatch   no_run       -
demo-e2e.yml                               push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705589
dependency-review.yml                      pull_request                 no_run       -
dep-graph.yaml                             pull_request                 no_run       -
dfa.yaml                                   push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153
docs-build.yaml                            push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705338
docs-deploy.yaml                           push                         queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705536
dr-cross.yaml                              schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313345565
edge-load.yaml                             schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429
egress.yml                                 push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705538
evidence.yaml                              push, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569079948
evidence-v01-smoke.yml                     push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705539
fuzz.yaml                                  push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705323
heartbeat-test.yaml                        pull_request, workflow_dispatch no_run       -
incident-e2e.yaml                          workflow_dispatch            no_run       -
incident-test.yaml                         push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108
integration.yaml                           push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706085
jwks-validate.yml                          push, workflow_dispatch      queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444
lean-morph.yml                             push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705506
lean-offline.yaml                          push, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705320
lean-style.yaml                            push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706852
loadtest.yaml                              pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626
marketplace-e2e.yaml                       push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631
morph-replay.yml                           push, workflow_dispatch      queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516
multiarch-build.yaml                       push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705304
nightly-replay.yml                         schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568693881
opa-test.yaml                              push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677
operational-excellence.yaml                push, pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399591865
paper-conformance.yaml                     push, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705694
pcs-ci.yml                                 push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705524
perf.yaml                                  schedule, workflow_dispatch  cancelled*   https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569153198
performance-gate.yaml                      push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705629
perf-proofmeter.yaml                       push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889
pf-ci.yaml                                 workflow_call                failure      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943
pf-cross-repo-consumer.yaml                pull_request, schedule       failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783
pf-reusable-caller.yaml                    pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28572843688
platform-cert-validate.yml                 push, pull_request, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691
platform-perf-smoke.yml                    push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706202
platform-replay.yml                        push, pull_request, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297
policy-build.yml                           push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162
policy-gates.yaml                          push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585707156
policy-pr-proof.yml                        pull_request                 no_run       -
pr-comments.yml                            pull_request                 no_run       -
privacy-test.yaml                          push, pull_request, schedule queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705511
proof-bot.yaml                             schedule, workflow_dispatch, issue_comment success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399500362
proof-fuzz.yaml                            push, pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882
proto-compat.yaml                          push, pull_request, schedule queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706169
publish-updates.yaml                       push, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888
rbac-test.yaml                             pull_request, workflow_dispatch no_run       -
redteam.yaml                               pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28312328896
release.yaml                               push, workflow_dispatch      no_run*      -
release-sbom.yml                           release                      no_run       -
replay.yml                                 push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517
retrieval-gateway.yml                      push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706166
reusable-ci-extended.yml                   workflow_call                no_run       -
reusable-ci-go-node.yml                    workflow_call                no_run       -
reusable-ci-lean.yml                       workflow_call                no_run       -
reusable-ci-prepare.yml                    workflow_call                no_run       -
reusable-ci-rust.yml                       workflow_call                no_run       -
revocation-sync.yaml                       schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470
sbom-diff.yaml                             push, pull_request, release  queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705575
scorecards.yml                             push, schedule, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706992
slo-gates.yaml                             push, pull_request, schedule skipped*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647128
spec-ai.yaml                               pull_request                 no_run       -
standards-pin.yml                          push, pull_request, workflow_dispatch queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705309
trust-fire-ga-test.yaml                    schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314313517
verify-publish-bundle.yaml                 push, pull_request, workflow_dispatch no_run*      -
wasm-scan.yaml                             push, pull_request           queued*      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705335

Summary: total=86 gated(push/schedule)=68 green=5 red=63 unknown=18
Markdown report written to C:\Users\mateo\provability-fabric\docs\internal\ci-inventory-latest.md

Gated workflows not green on last main run:
  - actionlint.yml (queued)
  - adapters-ci.yml (queued)
  - allowlist-sync.yaml (queued)
  - art-benchmark.yaml (failure)
  - bench-nightly-criterion.yaml (queued)
  - bench-swebench-smoke.yaml (queued)
  - bench-swebench-stress-scheduled.yaml (failure)
  - bench-swebench-unit.yaml (failure)
  - billing-test.yaml (failure)
  - cargo-deny.yml (queued)
  - cert-validate.yml (queued)
  - ci.yml (queued)
  - codeql.yaml (queued)
  - demo-e2e.yml (queued)
  - dfa.yaml (queued)
  - docs-build.yaml (queued)
  - docs-deploy.yaml (queued)
  - dr-cross.yaml (failure)
  - edge-load.yaml (failure)
  - egress.yml (queued)
  - evidence-v01-smoke.yml (queued)
  - fuzz.yaml (queued)
  - incident-test.yaml (failure)
  - integration.yaml (queued)
  - jwks-validate.yml (queued)
  - lean-morph.yml (queued)
  - lean-offline.yaml (queued)
  - lean-style.yaml (queued)
  - loadtest.yaml (failure)
  - marketplace-e2e.yaml (queued)
  - morph-replay.yml (queued)
  - multiarch-build.yaml (queued)
  - nightly-replay.yml (failure)
  - opa-test.yaml (failure)
  - operational-excellence.yaml (failure)
  - paper-conformance.yaml (queued)
  - pcs-ci.yml (queued)
  - perf.yaml (cancelled)
  - performance-gate.yaml (queued)
  - perf-proofmeter.yaml (failure)
  - pf-cross-repo-consumer.yaml (failure)
  - pf-reusable-caller.yaml (failure)
  - platform-cert-validate.yml (queued)
  - platform-perf-smoke.yml (queued)
  - platform-replay.yml (queued)
  - policy-build.yml (queued)
  - policy-gates.yaml (queued)
  - privacy-test.yaml (queued)
  - proof-fuzz.yaml (failure)
  - proto-compat.yaml (queued)
  - publish-updates.yaml (failure)
  - redteam.yaml (failure)
  - release.yaml (no_run)
  - replay.yml (queued)
  - retrieval-gateway.yml (queued)
  - revocation-sync.yaml (failure)
  - sbom-diff.yaml (queued)
  - scorecards.yml (queued)
  - slo-gates.yaml (skipped)
  - standards-pin.yml (queued)
  - trust-fire-ga-test.yaml (failure)
  - verify-publish-bundle.yaml (no_run)
  - wasm-scan.yaml (queued)
