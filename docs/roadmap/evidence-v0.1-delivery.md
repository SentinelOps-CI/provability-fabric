# Evidence v0.1 delivery guide

Historical guide for the fifteen stacked Evidence v0.1 pull requests. **Merged to `main` on 2026-06-14** (PRs #82–#96 into stacked bases; #97 landed `evidence-v01/testbed` on `main`).

## Stack order

Merge **in sequence**. Each PR targets the previous branch as base:

| PR | Head branch | Base branch | Title |
|----|-------------|-------------|-------|
| 1 | `evidence-v01/repo-hygiene` | `main` | docs: prepare repository for Evidence v0.1 stabilization |
| 2 | `evidence-v01/core-schemas` | `evidence-v01/repo-hygiene` | specs: add Evidence v0.1 artifact schemas |
| 3 | `evidence-v01/public-spec` | `evidence-v01/core-schemas` | docs: publish Evidence v0.1 model specification |
| 4 | `evidence-v01/fixtures` | `evidence-v01/public-spec` | test: add Evidence v0.1 fixtures and compatibility matrix |
| 5 | `evidence-v01/bundle-format` | `evidence-v01/fixtures` | cli: add Evidence v0.1 bundle packaging command |
| 6 | `evidence-v01/validator` | `evidence-v01/bundle-format` | cli: add strict validation for Evidence v0.1 bundles |
| 7 | `evidence-v01/e2e-example` | `evidence-v01/validator` | examples: add end-to-end Evidence v0.1 bundle walkthrough |
| 8 | `evidence-v01/runtime-binding` | `evidence-v01/e2e-example` | runtime: bind execution events to Evidence v0.1 artifacts |
| 9 | `evidence-v01/runtime-boundaries` | `evidence-v01/runtime-binding` | docs: document runtime evidence boundaries |
| 10 | `evidence-v01/runtime-scenario` | `evidence-v01/runtime-boundaries` | examples: add constrained runtime evidence scenario |
| 11 | `evidence-v01/replay-workflow` | `evidence-v01/runtime-scenario` | replay: add Evidence v0.1 replay verification workflow |
| 12 | `evidence-v01/replay-docs` | `evidence-v01/replay-workflow` | docs: document replay guarantees and limitations |
| 13 | `evidence-v01/forensic-example` | `evidence-v01/replay-docs` | examples: add forensic replay example |
| 14 | `evidence-v01/testbed` | `evidence-v01/forensic-example` | testbed: add Evidence v0.1 reproducible workflows |
| 15 | `evidence-v01/onboarding-docs` | `evidence-v01/testbed` | docs: add Evidence v0.1 onboarding and release notes |

## Manual compare links (historical)

If CLI auth is unavailable, open PRs via GitHub compare:

- [PR1: main...repo-hygiene](https://github.com/SentinelOps-CI/provability-fabric/compare/main...evidence-v01/repo-hygiene)
- [PR2: repo-hygiene...core-schemas](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/repo-hygiene...evidence-v01/core-schemas)
- [PR3: core-schemas...public-spec](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/core-schemas...evidence-v01/public-spec)
- [PR4: public-spec...fixtures](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/public-spec...evidence-v01/fixtures)
- [PR5: fixtures...bundle-format](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/fixtures...evidence-v01/bundle-format)
- [PR6: bundle-format...validator](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/bundle-format...evidence-v01/validator)
- [PR7: validator...e2e-example](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/validator...evidence-v01/e2e-example)
- [PR8: e2e-example...runtime-binding](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/e2e-example...evidence-v01/runtime-binding)
- [PR9: runtime-binding...runtime-boundaries](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/runtime-binding...evidence-v01/runtime-boundaries)
- [PR10: runtime-boundaries...runtime-scenario](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/runtime-boundaries...evidence-v01/runtime-scenario)
- [PR11: runtime-scenario...replay-workflow](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/runtime-scenario...evidence-v01/replay-workflow)
- [PR12: replay-workflow...replay-docs](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/replay-workflow...evidence-v01/replay-docs)
- [PR13: replay-docs...forensic-example](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/replay-docs...evidence-v01/forensic-example)
- [PR14: forensic-example...testbed](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/forensic-example...evidence-v01/testbed)
- [PR15: testbed...onboarding-docs](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v01/testbed...evidence-v01/onboarding-docs)

Set the **base** branch to the left side of each compare (e.g. PR2 base = `evidence-v01/repo-hygiene`).

## Review gates per PR

| PR | Minimum verification |
|----|-------------------|
| 1 | `mkdocs build`; no broken `AGENTS.md` refs |
| 2 | `python -m json.tool` on all six schemas |
| 4 | `pytest tests/evidence_schema -q`; CI `evidence-schema-only` job |
| 5 | `go test ./...` in `core/evidence`; `pytest tests/evidence_bundle -q` |
| 6 | above + `pytest tests/evidence_validation -q`; CI validator job |
| 7 | `pytest tests/e2e -q`; golden `expected/` comparison |
| 8 | `cargo test -p sidecar-watcher`; `pytest tests/runtime_evidence -q` |
| 10 | `bash examples/runtime-evidence-basic/run_scenario.sh` |
| 11 | `pytest tests/evidence_replay -q` |
| 14 | `bash testbed/evidence-v0.1/run_happy_path.sh`; full smoke workflow |
| 15 | Full quickstart in `docs/guides/evidence-v0.1-quickstart.md` |

### Progressive CI (`.github/workflows/evidence-v01-smoke.yml`)

| Stack position | Workflow behavior |
|----------------|-------------------|
| PR4 (`fixtures`) | `evidence-schema-only` job on `specs/evidence/**`, `tests/evidence_schema/**` |
| PR6 (`validator`) | Adds `core/evidence/**` paths, Go tests, `tests/evidence_validation` job |
| PR14 (`testbed`) | Full smoke: all pytest suites, testbed scripts, sidecar step when CERT-V1 present |

## Fresh-clone verification checklist

Run once before opening PRs (record result in status doc):

```bash
git clone --recurse-submodules https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric
git checkout evidence-v01/onboarding-docs
cd core/cli/pf && go build -o pf . && cd ../../..
pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay \
  tests/evidence_bundle tests/e2e tests/runtime_evidence tests/forensic_replay tests/testbed -q
cd core/evidence && go test ./... && cd ../..
cargo test -p sidecar-watcher -- write_evidence_binding write_cert_with_binding 2>/dev/null || cargo check -p sidecar-watcher
mkdocs build
./core/cli/pf/pf evidence validate \
  specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json --strict
```

**Local result (2026-06-14):** executed on `evidence-v01/onboarding-docs` tip — 37 pytest passed (1 skipped: live sidecar on Windows), `go test ./...` in `core/evidence` passed, `cargo test -p sidecar-watcher` binding tests passed (CERT-V1 live test skipped without submodule locally), `mkdocs build` passed.

## Post-merge hygiene

1. ~~Optional: delete remote branches `evidence-v01/*`~~ — **Done** except `evidence-v01/snapshot` (2026-06-14).
2. ~~Remove `scripts/create-evidence-v01-pr-stack.ps1`~~ — done on `main`.
3. Monitor `evidence-v01-smoke.yml` on `main` for regressions.
