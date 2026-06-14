# CI health matrix

Triage snapshot for `main` as of 2026-06-14 after Evidence v0.2 delivery closure (PRs #112–#114).

## Evidence gate (must stay green)

| Workflow | Job | Status | Notes |
|----------|-----|--------|-------|
| Evidence v0.1 smoke | evidence-schema-only, evidence-validator, smoke | Green | Baselines: [27512113090](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512113090) (#111), dispatch [27515098869](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27515098869) (closure sign-off) |
| Standards Pin Drift Check | check | Green | Uses `make submodules` + `make standards-pin-check` |
| Documentation Build | build-docs | Expected green | `mkdocs build --strict` + link-check (#114) |

## Standards / token parity

| Workflow | Known failure | Fix | Status |
|----------|---------------|-----|--------|
| docs-build | Private submodule checkout | Plain checkout + `make submodules` (#113/#114) | Fixed |
| cert-validate, replay, egress, platform-* | Same | Already on `make submodules` pattern | OK |
| nightly-replay | Invalid YAML (triplicate workflow definitions) | Deduplicated workflow (#115) | Fixed |

## Main CI (`ci.yml` reusable jobs)

| Workflow | Job | Known failure | Priority |
|----------|-----|---------------|----------|
| CI | prepare, lean, rust, go-node, extended | Queue-heavy; Lean mathlib vendor, sidecar tests | P1 |
| CI | protobuf-lint | Buf config drift | P2 |

## Platform legacy / optional lanes

| Workflow | Known failure | Owner area | Priority |
|----------|---------------|------------|----------|
| Platform CERT Validation | Missing `STANDARDS_GITHUB_TOKEN` on fork | Standards | P2 — secret required |
| Platform Replay Tests | KIT/submodule or fixture drift | Replay | P2 |
| Platform Performance Smoke Tests | Env/services not up on generic push | Platform | P3 |
| Performance Gate | Baseline not recorded | Bench | P3 |
| Paper Conformance CI | Lean/paper fixtures | Research | P3 |

## Bench

| Workflow | Known failure | Fix |
|----------|---------------|-----|
| Bench SWE-bench Smoke | OpenHands/env on Windows | Document WSL; mock engine path green |
| bench-swebench-unit | Provider env tests | Covered in stabilization matrix |

## Docker multi-arch

| Workflow | Known failure | Priority |
|----------|---------------|----------|
| Multi-Architecture Build & Deploy | Dockerfile deps, build context | P2 — investigate per service log |

## CLA / automation

| Workflow | Known failure | Fix | Status |
|----------|---------------|-----|--------|
| CLA Bot | Wrong org/repo in `cla/cla.json` | Point at `SentinelOps-CI/provability-fabric` | Fixed (#115) |
| CLA Bot | External CLA API unreachable | Requires hosted CLA service or disable check | Blocker — user action |

## Invalid or noisy workflow entries

| Workflow | Symptom | Fix | Status |
|----------|---------|-----|--------|
| nightly-replay.yml | Instant failure on every push (invalid YAML) | Single workflow definition | Fixed |
| demo-e2e.yml | Runs on all main pushes | Path filter on push | Fixed |
| pf-ci.yaml | `workflow_call` only — spurious failed check on push | No push trigger; caller via pf-reusable-caller | Waived — reusable only |

## Required secrets

| Secret | Workflows | Action if missing |
|--------|-----------|-------------------|
| `STANDARDS_GITHUB_TOKEN` | Evidence smoke, cert/replay/docs build, standards-pin | Add PAT with read access to `verifiable-ai-ci/*` |
| `GITHUB_TOKEN` | Default | Auto-provided |

## Local pre-PR gates

```bash
make dev-standards
make evidence-verify   # Evidence changes
make docs-strict       # docs/** or mkdocs.yml
```

See [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md) and [ci-reference.md](../reference/ci-reference.md).
