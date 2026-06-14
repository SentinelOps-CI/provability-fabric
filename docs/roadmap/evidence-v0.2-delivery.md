# Evidence v0.2 delivery guide

Historical guide for the eight stacked Evidence v0.2 pull requests plus CI hardening follow-ups. **Merged to `main` on 2026-06-14** (PRs #98–#104 into stacked bases; #105 landed `evidence-v02/onboarding` on `main`). CI hardening through #111.

## Stack order

Merge **in sequence**. Each PR targets the previous branch as base (except #105, which merges the stack tip onto `main`):

| PR | Head branch | Base branch | Title |
|----|-------------|-------------|-------|
| 98 | `evidence-v02/submodules` | `main` | Evidence v0.2: external standards submodules and pin-check |
| 99 | `evidence-v02/trace-adapter` | `evidence-v02/submodules` | Evidence v0.2: TRACE-REPLAY-KIT trace import adapter |
| 100 | `evidence-v02/schema-replay-context` | `evidence-v02/trace-adapter` | Evidence v0.2: schema and replay_context validation |
| 101 | `evidence-v02/deep-replay` | `evidence-v02/schema-replay-context` | Evidence v0.2: deep replay execution via KIT |
| 102 | `evidence-v02/runtime-e2e` | `evidence-v02/deep-replay` | Evidence v0.2: runtime evidence E2E and smoke hardening |
| 103 | `evidence-v02/lane-docs` | `evidence-v02/runtime-e2e` | Evidence v0.2: lane docs and separation tests |
| 104 | `evidence-v02/onboarding` | `evidence-v02/lane-docs` | Evidence v0.2: onboarding docs and roadmap |
| 105 | `evidence-v02/onboarding` | `main` | Evidence v0.2: land full stack on main |

## Manual compare links (historical)

If CLI auth is unavailable, open PRs via GitHub compare:

- [PR98: main...submodules](https://github.com/SentinelOps-CI/provability-fabric/compare/main...evidence-v02/submodules)
- [PR99: submodules...trace-adapter](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/submodules...evidence-v02/trace-adapter)
- [PR100: trace-adapter...schema-replay-context](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/trace-adapter...evidence-v02/schema-replay-context)
- [PR101: schema-replay-context...deep-replay](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/schema-replay-context...evidence-v02/deep-replay)
- [PR102: deep-replay...runtime-e2e](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/deep-replay...evidence-v02/runtime-e2e)
- [PR103: runtime-e2e...lane-docs](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/runtime-e2e...evidence-v02/lane-docs)
- [PR104: lane-docs...onboarding](https://github.com/SentinelOps-CI/provability-fabric/compare/evidence-v02/lane-docs...evidence-v02/onboarding)
- [PR105: main...onboarding](https://github.com/SentinelOps-CI/provability-fabric/compare/main...evidence-v02/onboarding)

Set the **base** branch to the left side of each compare (e.g. PR99 base = `evidence-v02/submodules`).

## Review gates per PR

Gates align with the [Evidence v0.2 definition of done](evidence-v0.2.md#definition-of-done):

| PR | Topic | Minimum verification |
|----|-------|---------------------|
| 98 | Submodules | `make dev-standards`; `make standards-pin-check` |
| 99 | Trace adapter | `go test ./...` in `core/evidence`; `pytest tests/evidence_trace -q` |
| 100 | v0.2 schema | v0.1 fixtures unchanged; v0.2 fixture validates; `pytest tests/evidence_schema -q` |
| 101 | Deep replay | `testbed/evidence-v0.2/run_deep_replay.sh --execute` |
| 102 | Runtime E2E | `cargo test -p sidecar-watcher -- emit_evidence`; Linux sidecar pytest |
| 103 | Lane docs | `pytest tests/evidence_schema/test_lane_separation.py -q` |
| 104 | Release docs | `mkdocs build`; quickstart v0.2 section |
| 105 | Land on main | Full Evidence smoke matrix green on Linux CI |

### CI hardening (post-merge, #106–#111)

| PR | Fix |
|----|-----|
| #106 | Remove broken `submodules: recursive` checkout |
| #107 | `STANDARDS_GITHUB_TOKEN` + `scripts/init_external_standards.sh` |
| #108 | Bash `pipefail` in init script |
| #109 | KIT Python deps in smoke workflow |
| #110 | Create testbed `out/` before replay report |
| #111 | Migrate remaining workflows off `submodules: recursive`; `main` workflow_dispatch smoke green (run `27512113090`) |

Green baselines: PR #110 (first full matrix after testbed fix) and PR #111 (`main` workflow_dispatch confirmation).

## Fresh-clone verification checklist

Run once on a clean machine before opening Evidence PRs (record result in [Evidence v0.2 status](evidence-v0.2-status.md)):

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric
git checkout main
make dev-standards   # CERT-V1 + TRACE-REPLAY-KIT submodules (see external/README.md)
make evidence-verify
cd core/cli/pf && go build -o pf . && cd ../../..

# v0.1 path
./core/cli/pf/pf evidence validate \
  specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json --strict

# v0.2 path
./core/cli/pf/pf evidence trace import \
  --kit-trace tests/replay/bundles/simple/trace.json \
  --out /tmp/execution-trace.json
./core/cli/pf/pf evidence validate \
  specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --strict --base-dir specs/evidence/v0.2/examples/valid
./core/cli/pf/pf evidence replay \
  --bundle specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --base-dir specs/evidence/v0.2/examples/valid \
  --execute --low-view

# Runtime (Linux; requires make submodules for CERT-V1 schema)
cargo test -p sidecar-watcher -- emit_evidence
mkdocs build
```

For CI and private upstream repos, set repository secret **`STANDARDS_GITHUB_TOKEN`** (see [`external/README.md`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/external/README.md)).

**Local shortcut:** `make evidence-verify` runs standards init, Go/pytest suites, and both testbed scripts (Linux/WSL or Git Bash on Windows).

## Post-merge hygiene

1. Optional: delete remote branches `evidence-v02/*` (keep documented archives such as `refs/backup/pre-split-evidence-v02` if retained).
2. Monitor [`evidence-v01-smoke.yml`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/evidence-v01-smoke.yml) on `main` for regressions; dispatch via Actions when validating delivery.
3. Ensure org/repo secret **`STANDARDS_GITHUB_TOKEN`** is configured for fork PRs and workflows that call `make submodules`.
4. Optional: delete remote `evidence-v01/*` branches after v0.1 archive policy is agreed (see [Evidence v0.1 delivery guide](evidence-v0.1-delivery.md#post-merge-hygiene)).
