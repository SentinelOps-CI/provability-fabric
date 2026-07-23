# Evidence v0.1 status

Completion tracker for the Evidence v0.1 workstream. Implementation and delivery to `main` completed 2026-06-14 (PRs #82â€“#97).

## Implementation (branch stack)

| Item | Branch artifact | Local verification |
|------|-----------------|-------------------|
| Schemas | `specs/evidence/v0.1/schemas/` | `python -m json.tool` on each schema |
| Public spec | `docs/specs/evidence-model-v0.1.md`, `evidence-bundle-v0.1.md` | `mkdocs build` |
| Fixtures + compatibility | `specs/evidence/v0.1/examples/`, compatibility matrix | `pytest tests/evidence_schema -q` |
| `pf evidence bundle pack` | `core/evidence/`, PR5 stack | `go test ./...` in `core/evidence`; `tests/evidence_bundle` pytest shim |
| `pf evidence validate --strict` | `core/evidence/validator.go` | `pytest tests/evidence_validation -q` (invalid JSON, missing schema, digest tamper) |
| `pf evidence replay` | `core/evidence/replay.go` | `pytest tests/evidence_replay -q` |
| Runtime binding | `evidence_v01_binding` JSONL events | `cargo test -p sidecar-watcher`; live sidecar test on Linux + CERT-V1 |
| Examples | `examples/evidence-basic/expected/`, runtime scenario script | e2e + runtime pytest |
| Testbed + CI smoke | progressive `evidence-v01-smoke.yml`, testbed scripts | full matrix on PR14+ |
| Onboarding | quickstart, CHANGELOG, mkdocs nav | `mkdocs build` |

Last full local matrix (on `evidence-v01/onboarding-docs`, 2026-06-14): see [Fresh-clone checklist](evidence-v0.1-delivery.md#fresh-clone-verification-checklist) in delivery guide.

## Gap closure (2026-06-14)

| Gap | Status |
|-----|--------|
| PR5 pytest shim for pack tests | Addressed â€” `tests/evidence_bundle/test_bundle_pack.py` |
| PR6 cert-validate.yml duplicate workflows | Addressed â€” single fail-closed workflow |
| PR6 validation pytest coverage | Addressed â€” invalid JSON, missing schema, bad-bundle-digest report |
| PR7 golden `expected/` outputs | Addressed â€” `examples/evidence-basic/expected/` |
| PR8 live sidecar + Rust unit tests | Addressed â€” `test_runtime_evidence_sidecar.py`, expanded Rust tests |
| PR10 live scenario script | Addressed â€” `run_scenario.sh` static + `--live` |
| PR4/6/14 progressive CI smoke | Addressed â€” schema-only â†’ validator â†’ full + sidecar step |
| PR15 delivery docs + script hygiene | Addressed â€” checklist, status update, post-merge script note |

## Delivery

| Gate | Status |
|------|--------|
| 15 stacked PRs opened and merged (#82â€“#96) | Complete |
| Stack landed on `main` (#97) | Complete |
| PR opener script removed | Complete |
| CI on GitHub | Evidence smoke green on Linux CI (PR #110 stack tip; PR #111 `main` workflow_dispatch run 27512113090, 2026-06-14); other repo-wide checks may still fail |
| Fresh-clone quickstart verified by independent reviewer | Complete (v0.2 matrix on `evidence-v02/integration`) |

See [Evidence v0.2 integration](../../roadmap/evidence-v0.2.md) and [Evidence v0.2 status](evidence-v0.2-status.md).

## Known limitations (v0.1 superseded by v0.2)

| v0.1 limitation | v0.2 status |
|-----------------|-------------|
| Static replay only | Addressed â€” `pf evidence replay --execute` |
| Manual external clone | Addressed â€” git submodules + `make dev-standards` |
| CI skips without CERT-V1 | Addressed â€” smoke job fails closed |
| PCS / so bundle confusion | Addressed â€” lane guide + negative tests (no schema merge) |
| Binding docs implied conditional | Addressed â€” binding always on emit; bundle ref optional |

## Out of scope (v0.1)

- Replacing PCS `EvidenceBundle.v0` admission
- Replacing `so bundle pack` spec tar archives
- Redefining CERT-V1 schema (external standard only)

## Verification commands

```bash
cd core/evidence && go test ./...
cd core/cli/pf && go build -o pf .
./pf evidence validate specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json --strict
pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay \
  tests/evidence_bundle tests/e2e tests/runtime_evidence tests/forensic_replay tests/testbed -q
bash testbed/evidence-v0.1/run_happy_path.sh
bash testbed/evidence-v0.1/run_tamper_case.sh
mkdocs build
```
