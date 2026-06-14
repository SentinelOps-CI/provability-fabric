# Evidence v0.2 status

Completion tracker for the Evidence v0.2 integration workstream. Implementation and delivery to `main` completed 2026-06-14 (PRs #98–#105); CI hardening through #110.

## Implementation (branch stack)

| Item | Branch artifact | Local verification |
|------|-----------------|-------------------|
| Submodules | `.gitmodules`, `make submodules`, `make standards-pin-check` | `make dev-standards` |
| Trace adapter | `core/evidence/trace_adapter.go`, `pf evidence trace import` | `go test ./...`; `pytest tests/evidence_trace -q` |
| v0.2 schema | `specs/evidence/v0.2/schemas/`, `replay_context` | v0.1 fixtures unchanged; v0.2 fixture validates |
| Deep replay | `kit_runner.go`, `--execute` / `--low-view` | `testbed/evidence-v0.2/run_deep_replay.sh --execute` |
| Runtime E2E | `emit_evidence_tests.rs`, smoke hardening | `cargo test -p sidecar-watcher emit_evidence`; Linux sidecar pytest |
| Lane docs | compatibility matrix, `test_lane_separation.py` | `pytest tests/evidence_schema/test_lane_separation.py -q` |
| Release docs | `docs/roadmap/evidence-v0.2.md`, CHANGELOG, mkdocs | `mkdocs build` |

Last full Evidence smoke matrix (Linux CI, 2026-06-14): all three jobs green (`evidence-schema-only`, `evidence-validator`, `smoke`). Green baselines: PR #110 (stack tip CI) and PR #111 (`main` workflow_dispatch run [27512113090](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512113090)).

## CI hardening (post-merge)

| Fix | PR | Outcome |
|-----|-----|---------|
| Remove broken `submodules: recursive` checkout | #106 | Checkout no longer fails on stale `vendor/mathlib` gitlink |
| Fetch private CERT-V1 / TRACE-REPLAY-KIT | #107 | `STANDARDS_GITHUB_TOKEN` + `scripts/init_external_standards.sh` |
| Bash for `pipefail` in init script | #108 | `make submodules` works on Ubuntu default shell |
| Install KIT Python deps in smoke | #109 | Deep replay `--execute` has `requests` et al. |
| Create testbed `out/` before replay report | #110 | `run_happy_path.sh` passes end-to-end |
| Migrate workflows off `submodules: recursive` | #111 | Plain checkout + `make submodules`; grep confirms zero `submodules:` usages |

## Delivery

| Gate | Status |
|------|--------|
| 7 stacked PRs opened and merged (#98–#104) | Complete |
| Stack landed on `main` (#105) | Complete |
| Evidence smoke green on Linux CI (#110) | Complete |
| `main` workflow_dispatch confirmation (#111, run 27512113090) | Complete |
| Remote branch cleanup (`evidence-v01/*`, `evidence-v02/*`) | Optional |

See [Evidence v0.2 integration](evidence-v0.2.md) for definition of done, [Evidence v0.2 delivery guide](evidence-v0.2-delivery.md) for stack and fresh-clone checklist, and [Evidence v0.1 status](evidence-v0.1-status.md) for the v0.1 baseline.

## Known limitations

| Item | Status |
|------|--------|
| Upstream tags `v1.0.0` not published | Pins use commit SHAs in `tools/standards/versions.json` |
| Private `verifiable-ai-ci/*` repos | CI requires `STANDARDS_GITHUB_TOKEN` secret |
| Other workflows using `submodules: recursive` | Complete — removed in #111; use plain checkout + `make submodules` |
| `mkdocs build --strict` | Complete — enforced in docs-build CI and `make docs-strict` |

## Out of scope (unchanged)

- Merging PCS `EvidenceBundle.v0` with Evidence JSON schemas
- Replacing `pf bundle pack` tar archives
- Vendoring CERT-V1 into the main repo

## Verification commands

```bash
make submodules && make standards-pin-check
cd core/evidence && go test ./...
cd core/cli/pf && go build -o pf .
./pf evidence trace import --kit-trace specs/evidence/v0.2/examples/valid/kit/trace.json --out /tmp/v01-trace.json
./pf evidence replay --bundle specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --base-dir specs/evidence/v0.2/examples/valid --execute --low-view
bash testbed/evidence-v0.1/run_happy_path.sh
bash testbed/evidence-v0.2/run_deep_replay.sh --execute
pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay \
  tests/evidence_trace tests/runtime_evidence tests/testbed -q
cargo test -p sidecar-watcher -- emit_evidence
bash scripts/check_cert_write_paths.sh
```
