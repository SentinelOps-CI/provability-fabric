CI workflow inventory - repo=SentinelOps-CI/provability-fabric branch=main
WORKFLOW                                   TRIGGERS                     STATUS       URL
--------------------------------------------------------------------------------------------------------------
actionlint.yml                             push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922330
adapters-ci.yml                            push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922311
allowlist-sync.yaml                        push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706271
art-benchmark.yaml                         push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401
bench-nightly-criterion.yaml               push, pull_request, schedule, workflow_dispatch in_progress* https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691442
bench-swebench-smoke.yaml                  push, pull_request, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705704
bench-swebench-stress-scheduled.yaml       schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314414940
bench-swebench-unit.yaml                   push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596576576
billing-test.yaml                          push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922315
bundle-check.yaml                          pull_request                 no_run       -
cargo-deny.yml                             push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691406
cert-validate.yml                          push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116959
chaos-nightly.yaml                         schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568878282
ci.yml                                     push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691498
ci-nightly-pytest.yml                      schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28576040030
ci-weekly-full.yml                         schedule, workflow_dispatch  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28367886347
cla-bot.yaml                               pull_request, workflow_dispatch failure      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318
codeql.yaml                                push, pull_request, schedule in_progress* https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691407
compliance.yaml                            release, workflow_dispatch   no_run       -
demo-e2e.yml                               push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705589
dependency-review.yml                      pull_request                 no_run       -
dep-graph.yaml                             pull_request                 no_run       -
dfa.yaml                                   push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647153
docs-build.yaml                            push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116934
docs-deploy.yaml                           push                         success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116948
dr-cross.yaml                              schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28313345565
edge-load.yaml                             schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429
egress.yml                                 push, pull_request, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705538
evidence.yaml                              push, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569079948
evidence-v01-smoke.yml                     push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116975
fuzz.yaml                                  push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691416
heartbeat-test.yaml                        pull_request, workflow_dispatch no_run       -
incident-e2e.yaml                          workflow_dispatch            no_run       -
incident-test.yaml                         push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108
integration.yaml                           push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691379
jwks-validate.yml                          push, workflow_dispatch      success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705444
lean-morph.yml                             push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922346
lean-offline.yaml                          push, schedule, workflow_dispatch cancelled*   https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922294
lean-style.yaml                            push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922304
loadtest.yaml                              pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626
marketplace-e2e.yaml                       push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705631
morph-replay.yml                           push, workflow_dispatch      success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516
multiarch-build.yaml                       push, pull_request, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691412
nightly-replay.yml                         schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28568693881
opa-test.yaml                              push, pull_request           failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677
operational-excellence.yaml                push, pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691421
paper-conformance.yaml                     push, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691431
pcs-ci.yml                                 push, pull_request, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705524
perf.yaml                                  schedule, workflow_dispatch  cancelled*   https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28569153198
performance-gate.yaml                      push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705629
perf-proofmeter.yaml                       push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889
pf-ci.yaml                                 workflow_call                failure      https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27677070943
pf-core-schema-check.yml                   push, pull_request           no_run*      -
pf-cross-repo-consumer.yaml                pull_request, schedule       failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783
pf-reusable-caller.yaml                    pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28572843688
platform-cert-validate.yml                 push, pull_request, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691
platform-perf-smoke.yml                    push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922281
platform-replay.yml                        push, pull_request, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297
policy-build.yml                           push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647162
policy-gates.yaml                          push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691427
policy-pr-proof.yml                        pull_request                 no_run       -
pr-comments.yml                            pull_request                 no_run       -
privacy-test.yaml                          push, pull_request, schedule success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691418
proof-bot.yaml                             schedule, workflow_dispatch, issue_comment failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28589794992
proof-fuzz.yaml                            push, pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882
proto-compat.yaml                          push, pull_request, schedule failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585706169
publish-updates.yaml                       push, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888
rbac-test.yaml                             pull_request, workflow_dispatch no_run       -
redteam.yaml                               pull_request, schedule, workflow_dispatch failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28312328896
release.yaml                               push, workflow_dispatch      no_run*      -
release-sbom.yml                           release                      no_run       -
replay.yml                                 push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517
retrieval-gateway.yml                      push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922316
reusable-ci-extended.yml                   workflow_call                no_run       -
reusable-ci-go-node.yml                    workflow_call                no_run       -
reusable-ci-lean.yml                       workflow_call                no_run       -
reusable-ci-prepare.yml                    workflow_call                no_run       -
reusable-ci-rust.yml                       workflow_call                no_run       -
revocation-sync.yaml                       schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470
sbom-diff.yaml                             push, pull_request, release  success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691430
scorecards.yml                             push, schedule, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28627691408
slo-gates.yaml                             push, pull_request, schedule skipped*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585647128
spec-ai.yaml                               pull_request                 no_run       -
standards-pin.yml                          push, pull_request, workflow_dispatch success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28625116949
trust-fire-ga-test.yaml                    schedule, workflow_dispatch  failure*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28314313517
verify-publish-bundle.yaml                 push, pull_request, workflow_dispatch no_run*      -
wasm-scan.yaml                             push, pull_request           success*     https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28622922329

Summary: total=87 gated(push/schedule)=69 green=33 red=35 unknown=19
