# CI health matrix

Triage and historical notes for `main`. **Live counts live in the inventory + tracker â€” not in the archived tables below.**

Automated inventory: `scripts/ci_workflow_inventory.sh --markdown` (bash/WSL) or `scripts/ci_workflow_inventory.ps1 -Markdown` (Windows). Latest report: [ci-inventory-latest.md](../ci-inventory-latest.md). Program sign-off: [evidence-program-closure.md](../../roadmap/evidence-program-closure.md). Findings map: [remediation-tracker.md](../remediation-tracker.md).

## Live posture (Wave 8 â€” authoritative)

| Metric | Value | Source |
|--------|------:|--------|
| Gated (push/schedule on `main`) | **69** | [ci-inventory-latest.md](../ci-inventory-latest.md) (2026-07-18) |
| Inventory exit | **0** (Ã—2 claimed) | [remediation-tracker.md](../remediation-tracker.md), [evidence-program-closure.md](../../roadmap/evidence-program-closure.md) |
| Wave 7 historical gate | **60/60** @ `7d48b3d4` / tip `b8b78b94` | Preâ€“Wave 8 revive baseline |
| Literal 67/67 or 68/68 | **Do not claim** | Honest ungates + Wave 8 smokes expanded the gated set |

Wave 8 revive (2026-07-18): **PR #215** re-gated leftovers with honest smokes; CI-local proofs for moto DR, mock registry publish/revocation, edge-load/loadtest asserts. Still live-secret only: production AWS DR, live multi-region SaaS, live registry publish, live revocation fetch. Runbook: [wave7-post-merge-runbook.md](../wave7-post-merge-runbook.md).

### Inventory automation

```bash
# Bash / WSL / Git Bash
scripts/ci_workflow_inventory.sh              # exit 0 when all gated workflows green
scripts/ci_workflow_inventory.sh --markdown   # writes docs/internal/ci-inventory-latest.md

# Windows PowerShell
scripts/ci_workflow_inventory.ps1 -Markdown
```

## Archived baseline (2026-07-03 â€” historical only)

**Do not use as current status.** Audit session 2 snapshot: **13/68** gated green on `main`; inventory exit **1**. Target language at the time was 68/68 with honest Wave 7 gates. That program closed at **60/60** exit 0 (Wave 7), then Wave 8 expanded gated coverage to **69** with inventory exit **0**. Superseded by the live posture table above.

**Phase 0â€“1 local prep (2026-07-03, archived):** Placeholder gate, CI honesty gate (`ci.yml`), replay contract, compose smoke, sidecar `integration_tests`, DSSE cross-lang, `retrieval-gateway.yml` â€” all later proved on `main` (Waves 1â€“8).

## Workflow cluster remediation checklist (Wave 7â€“8 â€” closed)

Clusters below were the Wave 7 greening program. Status reflects **postâ€“Wave 8** reality. Forward CI cost/honesty work is Wave 11+ (not a re-open of this matrix).

| Cluster | Workflows | Wave deps | Status | Notes |
|---------|-----------|-----------|--------|-------|
| **Replay** | `platform-replay.yml`, `nightly-replay.yml`, `replay.yml`, `morph-replay.yml`, `platform-cert-validate.yml` | Wave 1 (F10) | **Green (gated)** | Contract test + submodule `CMD []` on `main` |
| **Security** | `codeql.yaml`, `cargo-deny.yml`, `wasm-scan.yaml`, `scorecards.yml` | Wave 1 (F20) | **Green (gated)** | |
| **Lean** | `lean-offline.yaml`, `lean-style.yaml`, `lean-morph.yaml`, `paper-conformance.yaml` | Wave 3, 6 | **Green (gated)** | F24/F33 closed; `lean-offline-full` proven |
| **Platform** | `slo-gates.yaml`, `operational-excellence.yaml`, `billing-test.yaml`, `integration.yaml`, `demo-e2e.yml` | Waves 1, 5 | **Green (gated)** | |
| **Bench** | `bench-nightly-criterion.yaml`, `performance-gate.yaml`, `bench-swebench-smoke.yaml` | Wave 1 (F23) | **Green (gated)** | Criterion green on `main`; stress honesty â†’ Wave 10.4 |
| **Evidence (gate)** | `evidence-v01-smoke.yml`, `evidence.yaml`, `cert-validate.yml`, `standards-pin.yml` | Waves 0â€“2 | **Green** | Keep green; do not weaken |
| **Core CI** | `ci.yml`, `proto-compat.yaml`, `actionlint.yml` | Wave 0â€“1 | **Green** | Includes `ci-honesty` gate |
| **Remaining** | docker, marketplace, DR, automation | Wave 7â€“8 | **Green (gated)** with CI-local proofs | Live AWS/registry still secret-gated (Wave 13) |

---

## Historical triage notes (2026-06-15 / PR #118 era)

The sections below are **archived narrative** from the Evidence program CI hardening era. Per-workflow last-run URLs and â€œ13/68â€ / â€œ8/67â€ figures are **not current**. For live status, re-run inventory or open [ci-inventory-latest.md](../ci-inventory-latest.md).

## Evidence acceptance gap closure fixes (2026-06-17)

Merged via PR #134 (`ci/gap-closure-workflow-bumps`):

| Workflow | Fix | Status |
|----------|-----|--------|
| `allowlist-sync.yaml` | `actions/checkout@v3` â†’ `@v4` | Merged (#134) |
| `lean-style.yaml` | elan install via `lean-toolchain` | Merged (#134) |
| `performance-gate.yaml` | `actions/cache@v3` â†’ `@v4` | Merged (#134) |
| `integration.yaml` | `actions/cache@v3` â†’ `@v4` | Merged (#134) |

## Evidence gate (must stay green)

| Workflow | Job | Status | Notes |
|----------|-----|--------|-------|
| Evidence v0.1 smoke | evidence-schema-only, evidence-validator, smoke | Green | Baselines: [27512113090](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512113090) (#111), dispatch [27527807232](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27527807232) (post-#116 sign-off) |
| Standards Pin Drift Check | check | Green | Uses `make submodules` + `make standards-pin-check` |
| Documentation Build | build-docs | Green | `mkdocs build --strict` via `make docs-strict` / docs-build workflow |

## Standards / token parity

Verified on `main` (post-#118): each workflow below runs `make submodules` with `STANDARDS_GITHUB_TOKEN` in the job env.

| Workflow | `make submodules` + token | Notes |
|----------|---------------------------|-------|
| `docs-build.yaml` | Yes | Plain checkout + submodules (#113/#114) |
| `cert-validate.yml` | Yes | |
| `replay.yml` | Yes | Docker replay runner |
| `egress.yml` | Yes | |
| `standards-pin.yml` | Yes | Pin drift gate |
| `evidence-v01-smoke.yml` | Yes | Evidence gate |
| `platform-cert-validate.yml` | Yes | |
| `platform-replay.yml` | Yes | |
| `nightly-replay.yml` | Yes | Scheduled replay |
| `morph-replay.yml` | N/A | Uses in-repo `tests/replay/bundles` only |

`actions/upload-artifact@v3` â†’ `@v4` bump tracked in standards-parity PR (#119+).

## Main CI (`ci.yml` reusable jobs)

| Workflow | Job | Known failure | Priority | Fix in PR |
|----------|-----|---------------|----------|-----------|
| CI | prepare | â€” | â€” | Green (#118) |
| CI | protobuf-lint (buf) | â€” | â€” | Green (#116 proto dedup) |
| CI | lean | Stale `vendor/mathlib` cache without `.git` | P1 | `rm -rf` before vendor + script fix (#118) |
| CI | go-node | PCS handoff drift; heavy benchmark suite in unit job | P1 | Fixture pins + `pcsbench` build tag (#118) |
| CI | extended | k8s helm tests in lightweight job | P1 | Skip k8s paths; red-team offline (#118) |
| CI | rust | Long-running | P2 | Monitor |

## Protobuf Compatibility Tests (`proto-compat.yaml`)

| Job | Known failure | Fix | Status |
|-----|---------------|-----|--------|
| proto-lint | Missing `make proto-lint` | Added `scripts/proto.mk` targets | Fixed (#118) |
| proto-compat | Missing `make proto-gen-*` | Same Makefile include | Fixed (#118) |
| proto-* | `actions/upload-artifact@v3` deprecated | Bumped to v4 | Fixed (#116+) |
| proto-performance | Wrong protoc encode path | Covered by `make proto-gen-go` | Fixed (#118) |
| proto-go | protoc-gen-go not on PATH | `GOPATH/bin` in setup-go | Fixed (#118) |
| proto-ts/rust | Global npm/cargo plugin bins not on PATH | Append prefix/bin to `GITHUB_PATH` | Fixed (#118) |

## Actionlint

| Area | Known failure | Fix | Status |
|------|---------------|-----|--------|
| dr-cross.yaml | `local` in workflow script, bad matrix expr | Shell + expression fixes | Fixed (#118) |
| evidence.yaml | Inline Python confused shellcheck | `tools/compliance/generate_soc2_report.py` | Fixed (#118) |
| release.yaml | Broken `curl -d` quoting | Heredoc JSON payload | Fixed (#118) |
| demo-e2e.yml | Embedded Python YAML indent | Re-indented blocks | Fixed (#118) |
| Other workflows | Deprecated `actions/*@v3` runner warnings | `-ignore` for version migration (tech debt) | Waived in actionlint.yml |

## Platform legacy / optional lanes

| Workflow | Known failure | Owner area | Priority |
|----------|---------------|------------|----------|
| Platform CERT Validation | Missing `STANDARDS_GITHUB_TOKEN` | Standards | P2 â€” **secret required** |
| Platform Replay Tests | KIT/submodule or fixture drift | Replay | P2 |
| Platform Performance Smoke Tests | Env/services not up on generic push | Platform | P3 |
| Performance Gate | Baseline not recorded | Bench | P3 |
| Paper Conformance CI | Lean/paper fixtures | Research | P3 |
| Integration Tests | Kind/Helm admission timeout | Platform | P2 â€” dedicated `integration.yaml` |

## Bench

| Workflow | Known failure | Fix |
|----------|---------------|-----|
| Bench SWE-bench Smoke | OpenHands/env on Windows; PyYAML for policy packs | Document WSL; install pyyaml (#118) |
| bench-swebench-unit | Provider env tests | Covered in stabilization matrix |
| Bench Nightly Criterion | Compile + run benches on PR | P3 â€” optional lane |

## Docker multi-arch

| Workflow | Known failure | Priority | Fix |
|----------|---------------|----------|-----|
| Multi-Architecture Build & Deploy | Wrong build context (`/` vs service dir); invalid PR sha tag | P2 | Per-service `context` + `sha-` prefix (#118) |

## CLA / automation

| Workflow | Known failure | Fix | Status |
|----------|---------------|-----|--------|
| CLA Bot | Wrong org/repo in `cla/cla.json` | Point at `SentinelOps-CI/provability-fabric` | Fixed (#115) |
| CLA Bot | External CLA API unreachable | **Option B (#118):** no `push: main` on `cla-check`; skip when `/health` fails; PR-only advisory | Fixed (#118) |

## Invalid or noisy workflow entries

| Workflow | Symptom | Fix | Status |
|----------|---------|-----|--------|
| nightly-replay.yml | Instant failure on every push (invalid YAML) | Single workflow definition | Fixed |
| demo-e2e.yml | Runs on all main pushes | Path filter on push | Fixed |
| pf-ci.yaml | Stale push-era failures; `workflow_call` only | `workflow_dispatch` smoke (default) + full Kind via call/`mode=full`; caller via pf-reusable-caller | Smoke clears inventory; not a SaaS re-gate |

## Required secrets (org prerequisites)

### `STANDARDS_GITHUB_TOKEN` setup (org admin)

| Step | Action |
|------|--------|
| 1 | Create PAT (fine-grained or classic) with **read** on `verifiable-ai-ci/CERT-V1` and `verifiable-ai-ci/TRACE-REPLAY-KIT` |
| 2 | Repo **Settings â†’ Secrets and variables â†’ Actions â†’ New repository secret** |
| 3 | Name `STANDARDS_GITHUB_TOKEN`, paste PAT |
| 4 | Local check: `STANDARDS_GITHUB_TOKEN=<pat> make dev-standards` |
| 5 | CI check: `workflow_dispatch` **Evidence v0.1 smoke** or **Standards Pin Drift Check** â€” `make submodules` must pass |

**Status (2026-06-16):** Repository secret configured. Evidence smoke green on dispatch [27597765777](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765777).

Contributor-facing steps: [CONTRIBUTING.md â€” STANDARDS_GITHUB_TOKEN](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md).

| Secret / service | Workflows blocked | Action |
|------------------|-------------------|--------|
| `STANDARDS_GITHUB_TOKEN` | `platform-cert-validate.yml`, `cert-validate.yml`, `replay.yml`, `evidence-v01-smoke.yml`, `standards-pin.yml`, `docs-build.yaml`, `egress.yml`, `nightly-replay.yml`, `platform-replay.yml` | Org admin steps above; each workflow runs `make submodules` with `STANDARDS_GITHUB_TOKEN` env |
| CLA hosted service | `cla-bot.yaml` (PR + `workflow_dispatch` after #118) | **Option B applied:** no `push: main`; skip when CLA URL unreachable; dispatch smoke has no contributor range. Option A: restore hosted API at URL in `CLA/cla.json` |
| `CI_PAT` (optional) | `release.yaml` cross-repo dispatch | Only if release workflows must pass in closure sweep |
| `AWS_*` (optional) | `dr-cross.yaml`, `evidence.yaml` | Only if DR/evidence collection scheduled jobs are in scope |

| Secret | Workflows | Action if missing |
|--------|-----------|-------------------|
| `STANDARDS_GITHUB_TOKEN` | Evidence smoke, cert/replay/docs build, standards-pin, platform-cert/replay, egress, nightly-replay | Org admin: see setup table above |
| `GITHUB_TOKEN` | Default | Auto-provided |
| `CI_PAT` | release.yaml pf-testbed dispatch | Optional; release tags only |
| `AWS_*` | dr-cross, evidence collection | Optional; scheduled/AWS workflows only |

## Local pre-PR gates

```bash
make dev-standards
make evidence-verify   # Evidence changes
make docs-strict       # docs/** or mkdocs.yml
make proto-lint        # api/** or proto-compat workflow parity
make proto-validate
```

See [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md) and [ci-reference.md](../../reference/ci-reference.md).

## Workflow inventory (Phase 0 baseline â€” archived 2026-06-15)

**Archived.** Full inventory of `.github/workflows/*` on `main` as of 2026-06-15. Last-run status from that date is stale. **Live:** [ci-inventory-latest.md](../ci-inventory-latest.md) â€” **69** gated, inventory exit **0** (Wave 8). Do not cite the per-row â€œFailureâ€ URLs below as current.

Historical snapshot only: **85 workflows** then; many red/unknown. Closure criterion (push + schedule on `main` must be success) was later met via Wave 7 (**60/60**) then Wave 8 (**69** gated). Reusable-only (`workflow_call`) workflows are tracked but not gating until invoked.

| Bucket | Workflow | Triggers | Path filters | Last main run | Blocker |
|--------|----------|----------|--------------|---------------|---------|
| A â€” Core CI | `actionlint.yml` | push, pull_request | .github/workflows/** | Failure ([27527776628](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27527776628)) | in-repo fix |
|  | `adapters-ci.yml` | push, pull_request | adapters/**, .github/workflows/adapters-ci.yml | Failure ([26303694423](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/26303694423)) | in-repo fix |
|  | `bundle-check.yaml` | pull_request | bundles/** | No main run | in-repo fix |
|  | `ci-nightly-pytest.yml` | schedule, workflow_dispatch | â€” | Failure ([27542769271](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27542769271)) | in-repo fix |
|  | `ci-weekly-full.yml` | schedule, workflow_dispatch | â€” | Failure ([27546359989](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27546359989)) | in-repo fix |
|  | `ci.yml` | push, pull_request, workflow_dispatch | â€” | Failure ([27528984434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984434)) | in-repo fix |
|  | `dfa.yaml` | push, pull_request | core/lean-libs/ActionDSL/**, core/lean-tools/ExportDFA.lean, bundles/** | Failure ([17410006147](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006147)) | in-repo fix |
|  | `fuzz.yaml` | push, pull_request | runtime/sidecar-watcher/** | Failure ([27509871701](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27509871701)) | in-repo fix |
|  | `opa-test.yaml` | push, pull_request | runtime/admission-controller/opa/** | Failure ([16584478677](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/16584478677)) | in-repo fix |
|  | `pcs-ci.yml` | push, pull_request, workflow_dispatch | adapters/pcs/**, core/cli/pf/**, config/schemas/pcs/** (+30 more) | Failure ([27509871689](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27509871689)) | in-repo fix |
|  | `pf-ci.yaml` | workflow_call | â€” | Failure ([27528983101](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528983101)) | in-repo fix |
|  | `policy-build.yml` | push, pull_request | bundles/*/spec.yaml, bundles/*/proofs/*.lean | No main run | in-repo fix |
|  | `policy-gates.yaml` | push, pull_request | proofs/**, core/lean-libs/**, runtime/sidecar-watcher/** (+2 more) | Failure ([27515068287](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27515068287)) | in-repo fix |
|  | `privacy-test.yaml` | push, pull_request, schedule | runtime/privacy/**, runtime/sidecar-watcher/**, tools/privacy/** (+1 more) | Failure ([27509871685](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27509871685)) | in-repo fix |
|  | `proof-fuzz.yaml` | push, pull_request, schedule, workflow_dispatch | spec-templates/**, core/lean-libs/**, tests/proof-fuzz/** | Failure ([19399477882](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399477882)) | in-repo fix |
|  | `reusable-ci-extended.yml` | workflow_call | â€” | No main run | in-repo fix |
|  | `reusable-ci-go-node.yml` | workflow_call | â€” | No main run | in-repo fix |
|  | `reusable-ci-lean.yml` | workflow_call | â€” | No main run | in-repo fix |
|  | `reusable-ci-prepare.yml` | workflow_call | â€” | No main run | in-repo fix |
|  | `reusable-ci-rust.yml` | workflow_call | â€” | No main run | in-repo fix |
|  | `spec-ai.yaml` | pull_request | **/*.md, spec-templates/**, docs/specs/** | No main run | in-repo fix |
| B â€” Protobuf | `proto-compat.yaml` | push, pull_request, schedule | api/**, .github/workflows/proto-compat.yaml | Failure ([27529714646](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27529714646)) | in-repo fix |
| C â€” Standards | `cert-validate.yml` | push, pull_request, workflow_dispatch | evidence/**, tests/replay/**, external/** (+3 more) | Failure ([27515072768](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27515072768)) | org secret |
|  | `docs-build.yaml` | push, workflow_dispatch | bundles/**/spec.yaml, docs/**, mkdocs.yml (+2 more) | Failure ([27528984276](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984276)) | org secret |
|  | `docs-deploy.yaml` | push | docs/**, mkdocs.yml, .github/workflows/docs-deploy.yaml | Failure ([27528984316](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984316)) | in-repo fix |
|  | `egress.yml` | push, pull_request, workflow_dispatch | scripts/check-egress.sh, .github/workflows/egress.yml, external/** | Failure ([27512638971](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512638971)) | org secret |
|  | `evidence-v01-smoke.yml` | push, pull_request, workflow_dispatch | specs/evidence/**, core/evidence/**, core/cli/pf/evidence_commands.go (+20 more) | Green ([27527807232](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27527807232)) | org secret |
|  | `jwks-validate.yml` | push, workflow_dispatch | evidence/**, .github/workflows/jwks-validate.yml | Failure ([17535475445](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17535475445)) | in-repo fix |
|  | `morph-replay.yml` | push, workflow_dispatch | tests/replay/**, .github/workflows/morph-replay.yml | Failure ([17410006167](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006167)) | org secret |
|  | `nightly-replay.yml` | schedule, workflow_dispatch | â€” | Failure ([27530118488](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27530118488)) | org secret |
|  | `platform-cert-validate.yml` | push, pull_request, schedule | â€” | Failure ([27529897072](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27529897072)) | org secret |
|  | `platform-replay.yml` | push, pull_request, schedule | â€” | Failure ([27536776981](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27536776981)) | org secret |
|  | `replay.yml` | push, pull_request | tests/replay/**, external/TRACE-REPLAY-KIT/**, .github/workflows/replay.yml | Failure ([27510612216](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27510612216)) | org secret |
|  | `standards-pin.yml` | push, pull_request, workflow_dispatch | external/**, tools/standards/**, .gitmodules (+2 more) | Green ([27515072750](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27515072750)) | org secret |
| D â€” Supply chain | `cargo-deny.yml` | push, pull_request, workflow_dispatch | **/Cargo.toml, **/Cargo.lock, deny.toml | Failure ([27509871682](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27509871682)) | in-repo fix |
|  | `codeql.yaml` | push, pull_request, schedule | â€” | Failure ([27528984414](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984414)) | in-repo fix |
|  | `compliance.yaml` | release, workflow_dispatch | â€” | No main run | in-repo fix |
|  | `dep-graph.yaml` | pull_request | bundles/**/spec.yaml, tools/specgraph/**, .github/workflows/dep-graph.yaml | No main run | in-repo fix |
|  | `dependency-review.yml` | pull_request | â€” | No main run | in-repo fix |
|  | `evidence.yaml` | push, schedule, workflow_dispatch | â€” | Failure ([19399504758](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399504758)) | infra |
|  | `release-sbom.yml` | release | â€” | No main run | in-repo fix |
|  | `sbom-diff.yaml` | push, pull_request, release | â€” | Failure ([27528984306](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984306)) | in-repo fix |
|  | `scorecards.yml` | push, schedule, workflow_dispatch | â€” | Green ([27540655380](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27540655380)) | in-repo fix |
|  | `verify-publish-bundle.yaml` | push, pull_request, workflow_dispatch | experiments/scripts/verify_publish_bundle.py, experiments/scripts/publish_docs.py, experiments/scripts/publish_bundle.py (+8 more) | No main run | in-repo fix |
|  | `wasm-scan.yaml` | push, pull_request | registry/**, runtime/wasm-sandbox/**, .github/workflows/wasm-scan.yaml | Failure ([17750206124](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17750206124)) | in-repo fix |
| E â€” Platform / K8s | `billing-test.yaml` | push, pull_request, schedule | runtime/ledger/**, tools/billing/**, .github/workflows/billing-test.yaml | Failure ([19399598636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399598636)) | in-repo fix |
|  | `chaos-nightly.yaml` | schedule, workflow_dispatch | â€” | Failure ([19399539299](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399539299)) | infra |
|  | `demo-e2e.yml` | push, pull_request | demos/verifiable-mcp-fraud/**, .github/workflows/demo-e2e.yml | Failure ([27528983550](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528983550)) | infra |
|  | `dr-cross.yaml` | schedule, workflow_dispatch | â€” | Failure ([19399551209](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399551209)) | infra |
|  | `edge-load.yaml` | schedule, workflow_dispatch | â€” | Failure ([19417787429](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417787429)) | infra |
|  | `heartbeat-test.yaml` | pull_request, workflow_dispatch | runtime/sidecar-watcher/**, runtime/attestor/**, .github/workflows/heartbeat-test.yaml | No main run | infra |
|  | `incident-e2e.yaml` | workflow_dispatch | â€” | No main run | infra |
|  | `incident-test.yaml` | push, pull_request, schedule | runtime/incident-bot/**, ops/crd/**, ops/flux/** (+1 more) | Failure ([19399492108](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399492108)) | infra |
|  | `integration.yaml` | pull_request | runtime/**, tests/integration/**, .github/workflows/integration.yaml | No main run | infra |
|  | `loadtest.yaml` | pull_request, schedule, workflow_dispatch | runtime/** | Failure ([19399924626](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399924626)) | infra |
|  | `marketplace-e2e.yaml` | push, pull_request, workflow_dispatch | marketplace/**, .github/workflows/marketplace-e2e.yaml | Failure ([17508000336](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17508000336)) | infra |
|  | `operational-excellence.yaml` | push, pull_request, schedule, workflow_dispatch | â€” | Failure ([19399591865](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399591865)) | in-repo fix |
|  | `pf-cross-repo-consumer.yaml` | pull_request, schedule | â€” | Failure ([19399838783](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399838783)) | in-repo fix |
|  | `pf-reusable-caller.yaml` | pull_request, schedule | â€” | Failure ([19399912569](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399912569)) | in-repo fix |
|  | `platform-perf-smoke.yml` | push, pull_request | â€” | Failure ([27528984287](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984287)) | infra |
|  | `rbac-test.yaml` | pull_request, workflow_dispatch | runtime/ledger/**, core/cli/pf/**, .github/workflows/rbac-test.yaml | No main run | in-repo fix |
|  | `redteam.yaml` | pull_request, schedule, workflow_dispatch | runtime/**, tests/redteam/** | Failure ([19399052268](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399052268)) | in-repo fix |
|  | `trust-fire-ga-test.yaml` | schedule, workflow_dispatch | â€” | Failure ([27491601509](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27491601509)) | infra |
| F â€” Bench / perf | `art-benchmark.yaml` | push, pull_request, schedule | â€” | Failure ([19399502401](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399502401)) | in-repo fix |
|  | `bench-nightly-criterion.yaml` | push, pull_request, schedule, workflow_dispatch | bench/**, runtime/sidecar-watcher/**, Cargo.toml (+2 more) | Failure ([27530634250](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27530634250)) | in-repo fix |
|  | `bench-swebench-smoke.yaml` | push, pull_request, schedule, workflow_dispatch | bench/swebench/**, bench/fixtures/**, tests/test_swebench_runner_smoke.py (+1 more) | Failure ([27544642979](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27544642979)) | in-repo fix |
|  | `bench-swebench-stress-scheduled.yaml` | schedule, workflow_dispatch | â€” | Failure ([27491683161](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27491683161)) | in-repo fix |
|  | `bench-swebench-unit.yaml` | push, pull_request | bench/swebench/**, experiments/**, tests/test_*.py (+1 more) | No main run | in-repo fix |
|  | `lean-morph.yml` | push, pull_request, workflow_dispatch | **/*.lean, **/lakefile.lean, .github/workflows/lean-morph.yml | Failure ([17410006183](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006183)) | in-repo fix |
|  | `lean-offline.yaml` | push, pull_request, workflow_dispatch | **/*.lean, **/lakefile.lean, **/lean-toolchain (+1 more) | Failure ([17410006180](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006180)) | in-repo fix |
|  | `lean-style.yaml` | push, pull_request, workflow_dispatch | **/*.lean, scripts/check-dup-lean.sh | Failure ([17410006184](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006184)) | in-repo fix |
|  | `paper-conformance.yaml` | push, pull_request, schedule | â€” | Failure ([27529936688](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27529936688)) | in-repo fix |
|  | `perf-proofmeter.yaml` | push, pull_request, schedule | â€” | Failure ([19417776889](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19417776889)) | in-repo fix |
|  | `perf.yaml` | schedule, workflow_dispatch | â€” | Failure ([27530791650](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27530791650)) | in-repo fix |
|  | `performance-gate.yaml` | push, pull_request, workflow_dispatch | â€” | Failure ([27528984335](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984335)) | in-repo fix |
|  | `slo-gates.yaml` | push, pull_request, schedule | â€” | Failure ([19399612659](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399612659)) | in-repo fix |
| G â€” Docker | `multiarch-build.yaml` | push, pull_request, workflow_dispatch | â€” | Failure ([27528984267](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984267)) | in-repo fix |
|  | `publish-updates.yaml` | push, schedule, workflow_dispatch | tools/metrics/**, .github/workflows/publish-updates.yaml | Failure ([19399543888](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399543888)) | in-repo fix |
| H â€” Automation | `allowlist-sync.yaml` | push, pull_request | core/lean-libs/**, bundles/**/proofs/**, tools/gen_allowlist_from_lean.py (+1 more) | Failure ([17410006157](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/17410006157)) | in-repo fix |
|  | `cla-bot.yaml` | push, pull_request | â€” | Failure ([27528984318](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27528984318)) | external service |
|  | `policy-pr-proof.yml` | pull_request | policies/**, bundles/**, core/lean-libs/** (+3 more) | No main run | in-repo fix |
|  | `pr-comments.yml` | pull_request | â€” | No main run | in-repo fix |
|  | `proof-bot.yaml` | schedule, workflow_dispatch, issue_comment | â€” | Green ([19399500362](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19399500362)) | in-repo fix |
|  | `release.yaml` | push, workflow_dispatch | â€” | No main run | org secret |
|  | `revocation-sync.yaml` | schedule, workflow_dispatch | â€” | Failure ([19400248470](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/19400248470)) | in-repo fix |

### Inventory stats (archived 2026-06-17 â€” not live)

- Total workflow files then: **85**
- Gated then: **67**; green then: **12**; red: **52**; unknown: **21**
- Inventory exit then: **1**

**Live (Wave 8):** total workflow files **87**; gated **69**; inventory exit **0**. See [ci-inventory-latest.md](../ci-inventory-latest.md) and [evidence-program-closure.md](../../roadmap/evidence-program-closure.md).

### Blocker summary (archived)

Historical blockers (CLA hosted API, org secrets, Kind/AWS infra, in-repo fixes) were triaged through Waves 1â€“8. Remaining forward items are **live-secret** AWS DR / registry publish / revocation (Wave 13) and CI cost/honesty (Wave 11) â€” not a return to the 13/68 red matrix.

Automated check: `scripts/ci_workflow_inventory.sh` (exits non-zero when any push/schedule workflow last run on `main` is not success).
