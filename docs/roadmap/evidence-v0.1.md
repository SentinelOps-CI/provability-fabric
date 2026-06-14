# Evidence v0.1 roadmap

Evidence v0.1 delivers a minimal, reusable, validated path for packaging, validating, binding, replaying, and documenting verifiable evidence artifacts in Provability Fabric.

## Definition of done

- JSON Schemas under `specs/evidence/v0.1/schemas/`
- Public specification and compatibility docs
- Valid and invalid fixtures with pytest coverage
- CLI namespace `pf evidence` with `bundle pack`, `validate --strict`, and `replay`
- Runtime additive binding events without breaking CERT-V1
- Examples, testbed scripts, CI smoke workflow, and onboarding docs

## Fifteen-PR technical sequence

| PR | Topic | Deliverables |
|----|-------|--------------|
| 1 | Hygiene | This roadmap, AGENTS link fixes, placeholder paths |
| 2 | Schemas | Six JSON schemas + README |
| 3 | Public spec | Model + bundle format docs |
| 4 | Fixtures | Valid/invalid examples, compatibility matrix, schema tests |
| 5 | Pack CLI | `core/evidence` pack + `pf evidence bundle pack` |
| 6 | Validator | Strict validate, fail-closed cert validator |
| 7 | E2E example | `examples/evidence-basic`, walkthrough, e2e tests |
| 8 | Runtime binding | Sidecar `evidence_v01_binding` JSONL events |
| 9 | Runtime boundaries | Boundaries guide |
| 10 | Runtime scenario | `examples/runtime-evidence-basic` |
| 11 | Replay workflow | `pf evidence replay`, `core/evidence/replay.go` |
| 12 | Replay docs | Replay guarantees guide |
| 13 | Forensic example | Pass/tamper forensic walkthrough |
| 14 | Testbed | `testbed/evidence-v0.1` scripts + CI smoke |
| 15 | Onboarding | Quickstart, status doc, CHANGELOG, mkdocs nav |

## Current platform map

| Surface | Role relative to v0.1 |
|---------|------------------------|
| CERT-V1 sidecar certs | Compatible attestation artifact type (external schema) |
| TRACE-REPLAY-KIT (`so trace …`) | Execution trace input; not replaced by v0.1 replay |
| PCS `EvidenceBundle.v0` | Related science-claim domain; documented separately |
| `so bundle pack` | Spec tar archives; out of scope for v0.1 JSON bundles |

## Known limitations (honest)

- `pf check-trace` only verifies that `bundles/` exists; it is not a traceability validator.
- `replayStatusCmdNew()` exists but is not registered; `replay status` uses the legacy handler.

### Historical limitations (resolved in v0.2)

- ~~`tools/cert-validate/validate.py` exited 0 when the external CERT-V1 schema was missing~~ — strict mode now fails closed unless `--allow-missing-schema` is passed; CI smoke requires CERT-V1 via `make submodules`.
- ~~Manual external clone for CERT-V1 / KIT~~ — git submodules + `make dev-standards` (see [Evidence v0.2 status](evidence-v0.2-status.md)).
- ~~CI skipped evidence checks without CERT-V1~~ — smoke job fails closed when standards are unavailable.
- ~~Windows: replay integration tests skipped without bash or external clones~~ — use WSL/Git Bash + `make dev-standards`; testbed scripts run under bash in CI.

## VERSION vs tags

Root [`VERSION`](../../VERSION) tracks the next platform release marker. Git tags (for example `v1.9.2`) reflect historical releases. Do not assume they match without checking release notes.

## Pre-PR 0 baseline results

Recorded on Windows checkout at `65bee159035e38e7a8f907ce2773226eca1ea4f3` (clean `main`):

| Command | Result | Notes |
|---------|--------|-------|
| `go test ./...` (`core/cli/pf`) | Fail | Pre-existing `pf/cmd` PCS test failures |
| `go build -o pf .` (`core/cli/pf`) | Pass | |
| `cargo test --workspace --exclude sidecar-watcher` | Fail | `labeler` stress tests |
| `cargo test -p sidecar-watcher` | Fail | Windows linker `LNK1104` contention |
| `python tools/cert-validate/validate.py --help` | Pass | |
| `mkdocs build` | Pass | Pre-existing unrelated link warnings |
| `make validate-certs` | Pass (vacuous) | Schema missing before fail-closed fix |
| `make no-runtime-placeholders` | Fail | Scans `build/` after mkdocs |

`external/CERT-V1/` is absent unless cloned per [`external/README.md`](../../external/README.md).

## Status

See [Evidence v0.1 status](evidence-v0.1-status.md) for the v0.1 completion checklist and [Evidence v0.2 status](evidence-v0.2-status.md) for current CI and delivery state.
