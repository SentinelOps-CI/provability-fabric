# CI health matrix

Triage snapshot for `main` as of 2026-06-15 after CI hardening PR (post-#117).

## Evidence gate (must stay green)

| Workflow | Job | Status | Notes |
|----------|-----|--------|-------|
| Evidence v0.1 smoke | evidence-schema-only, evidence-validator, smoke | Green | Baselines: [27512113090](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512113090) (#111), dispatch [27527807232](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27527807232) (post-#116 sign-off) |
| Standards Pin Drift Check | check | Green | Uses `make submodules` + `make standards-pin-check` |
| Documentation Build | build-docs | Investigate | `mkdocs build --strict` — failures may be link/submodule related on generic pushes |

## Standards / token parity

| Workflow | Known failure | Fix | Status |
|----------|---------------|-----|--------|
| docs-build | Private submodule checkout | Plain checkout + `make submodules` (#113/#114) | Fixed |
| cert-validate, replay, egress, platform-* | Same | Already on `make submodules` pattern | OK |
| nightly-replay | Invalid YAML (triplicate workflow definitions) | Deduplicated workflow (#115) | Fixed |

## Main CI (`ci.yml` reusable jobs)

| Workflow | Job | Known failure | Priority | Fix in PR |
|----------|-----|---------------|----------|-----------|
| CI | prepare | — | — | Green on main |
| CI | protobuf-lint (buf) | — | — | Green (#116 proto dedup) |
| CI | lean | Stale `vendor/mathlib` cache without `.git` | P1 | `rm -rf` before vendor + script fix |
| CI | go-node | `npm ci` path / prisma chain | P1 | Subshell install steps |
| CI | extended | Live red-team without kernel | P1 | `--offline` corpus validation in CI |
| CI | rust | Long-running | P2 | Monitor |

## Protobuf Compatibility Tests (`proto-compat.yaml`)

| Job | Known failure | Fix | Status |
|-----|---------------|-----|--------|
| proto-lint | Missing `make proto-lint` | Added `scripts/proto.mk` targets | Fixed |
| proto-compat | Missing `make proto-gen-*` | Same Makefile include | Fixed |
| proto-* | `actions/upload-artifact@v3` deprecated | Bumped to v4 | Fixed (#116+) |
| proto-performance | Wrong protoc encode path | Covered by `make proto-gen-go` | Fixed |

## Actionlint

| Area | Known failure | Fix | Status |
|------|---------------|-----|--------|
| dr-cross.yaml | `local` in workflow script, bad matrix expr | Shell + expression fixes | Fixed |
| evidence.yaml | Inline Python confused shellcheck | `tools/compliance/generate_soc2_report.py` | Fixed |
| release.yaml | Broken `curl -d` quoting | Heredoc JSON payload | Fixed |
| Other workflows | Deprecated `actions/*@v3` runner warnings | `-ignore` for version migration (tech debt) | Waived in actionlint.yml |

## Platform legacy / optional lanes

| Workflow | Known failure | Owner area | Priority |
|----------|---------------|------------|----------|
| Platform CERT Validation | Missing `STANDARDS_GITHUB_TOKEN` | Standards | P2 — **secret required** |
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
| CLA Bot | External CLA API unreachable | Requires hosted CLA service or disable check | **Blocker — org action** |

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

See [CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md) and [ci-reference.md](../reference/ci-reference.md).
