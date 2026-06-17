# Evidence v0.2 status

Completion tracker for the Evidence v0.2 integration workstream. Implementation and delivery to `main` completed 2026-06-14 (PRs #98–#105); CI hardening through #118 (merged 2026-06-16); evidence acceptance gap docs through #130 (merged 2026-06-16).

## Public status checkpoint 2026-06-16

| Item | Status |
|------|--------|
| **Main SHA** | `9788bb8a` (merge #130 evidence acceptance gap analysis) |
| **D1–D2** Schema + bundle tooling | Complete — v0.1/v0.2 schemas, `pf evidence validate --strict`, compatibility matrix |
| **D3** Runtime integration | Complete on Linux CI — sidecar binding + cert path guard; Windows `cargo test` deferred to CI authority |
| **D4** Replay | Complete — v0.1 static + v0.2 deep execute/low-view; cross-platform testbed hardening in gap-closure PR |
| **D5** Verification | Evidence smoke green; standards pins verified; program closure docs #127–#130 |
| **Attestation signatures** | Structural + digest-bound only; DSSE verification external ([attestation signatures](../specs/evidence-attestation-signatures.md)) |
| **Proof semantics** | Structural + digest-bound only; no Lean checking in Evidence lane |
| **Docs** | `mkdocs build --strict` passes on maintainer host |

### Explicit non-claims

- **Not** full-repo CI green (inventory: 8/67 gated workflows green on post-#128 `main`)
- **Not** Windows-local `cargo test emit_evidence` when crates.io SSL blocks downloads
- **Not** in-validator CERT-V1 / attestation signature verification (`--verify-signatures` out of scope)
- **Not** semantic proof checking (Lean) inside `pf evidence validate`

### CI authority (Linux)

| Gate | Run |
|------|-----|
| Evidence smoke (validate, replay, testbeds, runtime pytest) | [27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269) |
| Core CI | [27616317486](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616317486) |

Internal evidence acceptance positioning: [evidence-acceptance-positioning.md](../internal/evidence-acceptance-positioning.md). Suggested tag (optional, not created): `evidence-v0.2.0-acceptance`.

## CI hardening #118 (merged)

| Item | Detail |
|------|--------|
| Merge commit | `3f150b1569b8dd50061d57ed99f34aa4b8dfffe6` |
| Post-merge smoke | [workflow_dispatch 27596580912](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27596580912) |
| Closure stack | #121–#128 (`ci/standards-parity` … `ci/post-closure-hotfixes`) |
| Sign-off page | [evidence-program-closure.md](evidence-program-closure.md) (#127); hotfixes **#128** merged `de104223`; post-#128 sign-off **#129** merged `fdca37c4` |
| Post-#128 ceremony | Smoke [27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269), CI [27616317486](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616317486) |
| Phase 6 ceremony | Smoke [27597765777](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765777), CI [27597765883](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27597765883) |

## External standards verification (2026-06-16)

| Check | `main` SHA | Result |
|-------|------------|--------|
| `make dev-standards` | `fdca37c4` | **Pass** locally (CERT-V1 + TRACE-REPLAY-KIT submodules initialized) |
| `make standards-pin-check` | `fdca37c4` | **Pass** locally — pins match `tools/standards/versions.json` |
| CI smoke (`STANDARDS_GITHUB_TOKEN`) | `de104223` | **Pass** — [run 27616315269](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27616315269) (`make submodules` in Linux CI) |

Org secret `STANDARDS_GITHUB_TOKEN` is configured for CI; local clones use HTTPS submodule URLs when the token is not present.

## Acceptance verification record (2026-06-16)

Maintainer packet (private, gitignored): `private/acceptance-evidence/acceptance-2026-06-16/`

| Gate | Local (`fdca37c4`) | CI authority |
|------|-------------------|--------------|
| `pf evidence validate` v0.1/v0.2 `--strict` | Pass | smoke job in 27616315269 |
| `pf evidence replay --execute --low-view` | Pass (Windows; `PYTHONIOENCODING=utf-8`) | smoke job in 27616315269 |
| `mkdocs build --strict` | Pass | Documentation Build on PR #129 |
| Repo-wide inventory | exit 1 (8/67 gated green) | N/A — see [program closure](evidence-program-closure.md) |

Deep replay report archived at `private/acceptance-evidence/acceptance-2026-06-16/evidence-v02-replay-report.json`.

## CI inventory caveat

Evidence smoke and standards-pin baselines are green. The repository is **not** fully green repo-wide — inventory on `main` post-#128: **8/67** gated workflows green (exit 1). See [evidence-program-closure.md](evidence-program-closure.md).

## Implementation (branch stack)

| Item | Branch artifact | Local verification |
|------|-----------------|-------------------|
| Submodules | `.gitmodules`, `make submodules`, `make standards-pin-check` | `make dev-standards` |
| Trace adapter | `core/evidence/trace_adapter.go`, `pf evidence trace import` | `go test ./...`; `pytest tests/evidence_trace -q` |
| v0.2 schema | `specs/evidence/v0.2/schemas/`, `replay_context` | v0.1 fixtures unchanged; v0.2 fixture validates |
| Deep replay | `kit_runner.go`, `--execute` / `--low-view` | `testbed/evidence-v0.2/run_deep_replay.sh --execute` |
| Runtime E2E | `emit_evidence_tests.rs`, smoke hardening | `cargo test -p sidecar-watcher emit_evidence`; Linux sidecar pytest |
| Lane docs | compatibility matrix, `test_lane_separation.py` | `pytest tests/evidence_schema/test_lane_separation.py -q` |
| Release docs | `docs/roadmap/evidence-v0.2.md`, CHANGELOG, mkdocs | `mkdocs build --strict` |

Last full Evidence smoke matrix (Linux CI, 2026-06-15): all three jobs green (`evidence-schema-only`, `evidence-validator`, `smoke`). Green baselines: PR #110, PR #111 dispatch [27512113090](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27512113090), closure dispatch [27515098869](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27515098869), and post-#116 dispatch [27527807232](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/27527807232) (`5394d092`).

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
| Remote branch cleanup (`evidence-v01/*`, `evidence-v02/*`) | Complete — deleted 2026-06-14; kept `evidence-v01/snapshot` |
| Fresh-clone checklist recorded | Complete — see [Evidence v0.2 delivery guide](evidence-v0.2-delivery.md#fresh-clone-verification-checklist) (2026-06-14, commit on `main`) |
| mkdocs strict + docs-build CI | Complete — #114 |

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
