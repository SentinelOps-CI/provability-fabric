# Evidence v0.2 integration

Evidence v0.2 closes v0.1 limitation areas without breaking v0.1 bundles. v0.2 is opt-in via `schema_version: "0.2"` and optional `replay_context`.

## Definition of done

| Phase | Outcome | Verification |
|-------|---------|--------------|
| Submodules | `.gitmodules`, `make submodules`, `make standards-pin-check`, `make dev-standards` | Fresh clone + pin check |
| Trace adapter | `pf evidence trace import` KIT → v0.1 execution-trace | `go test` + `tests/evidence_trace` |
| v0.2 schema | `replay_context` in bundle schema + pack/validate | v0.1 fixtures unchanged; v0.2 fixture validates |
| Deep replay | `pf evidence replay --execute [--low-view]` | `testbed/evidence-v0.2/run_deep_replay.sh --execute` |
| Runtime E2E | Emit integration test + binding always documented | `cargo test emit_evidence` |
| Lane docs | Compatibility matrix + negative pytest | `tests/evidence_schema/test_lane_separation.py` |
| CERT ergonomics | Graceful test skip without schema panic | `cargo test -p sidecar-watcher` without submodules (unit skip) |
| Release docs | Roadmap, CHANGELOG, mkdocs nav | `mkdocs build --strict` (Complete) |

## v0.1 limitations superseded

| v0.1 limitation | v0.2 outcome |
|-----------------|--------------|
| Static replay only | `--execute` runs TRACE-REPLAY-KIT after static checks |
| Manual external clone | Git submodules + Makefile targets |
| CI skips without CERT-V1 | Smoke job requires schema; sidecar tests fail closed |
| PCS/so bundle confusion | Lane guide + negative tests (no schema merge) |
| Binding docs implied conditional emit | Binding JSONL always on emit path; bundle ref optional |

## Out of scope (unchanged)

- Merging PCS `EvidenceBundle.v0` with Evidence schemas
- Replacing `pf bundle pack` tar archives
- Vendoring CERT-V1 into the main repo

## Verification matrix

```bash
make submodules && make standards-pin-check
cd core/evidence && go test ./...
cd core/cli/pf && go build -o pf .
./pf evidence trace import --kit-trace tests/replay/bundles/simple/trace.json --out /tmp/v01-trace.json
./pf evidence replay --bundle specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --base-dir specs/evidence/v0.2/examples/valid --execute --low-view
cargo test -p sidecar-watcher -- emit_evidence
pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay \
  tests/evidence_trace tests/runtime_evidence tests/testbed -q
bash scripts/check_cert_write_paths.sh
mkdocs build --strict
```

## Related docs

- [Evidence v0.1 status](evidence-v0.1-status.md)
- [Compatibility matrix](../specs/evidence-compatibility.md)
- [Replay guarantees](../guides/replay-guarantees.md)
