# Evidence v0.1 status

Honest completion tracker for the Evidence v0.1 workstream. Distinguishes **implementation on branches** from **delivery to `main`**.

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
| PR5 pytest shim for pack tests | Addressed — `tests/evidence_bundle/test_bundle_pack.py` |
| PR6 cert-validate.yml duplicate workflows | Addressed — single fail-closed workflow |
| PR6 validation pytest coverage | Addressed — invalid JSON, missing schema, bad-bundle-digest report |
| PR7 golden `expected/` outputs | Addressed — `examples/evidence-basic/expected/` |
| PR8 live sidecar + Rust unit tests | Addressed — `test_runtime_evidence_sidecar.py`, expanded Rust tests |
| PR10 live scenario script | Addressed — `run_scenario.sh` static + `--live` |
| PR4/6/14 progressive CI smoke | Addressed — schema-only → validator → full + sidecar step |
| PR15 delivery docs + script hygiene | Addressed — checklist, status update, post-merge script note |

## Delivery (not complete until merged)

| Gate | Status |
|------|--------|
| 15 stacked PRs opened on GitHub | Pending — requires `gh auth login` |
| CI green on each PR | Pending — runs after PRs exist |
| Review + merge 1→15 to `main` | Pending |
| Fresh-clone quickstart verified by reviewer | Pending |
| Private delivery tracker (outside repo) | Maintainer responsibility |

See [Evidence v0.1 delivery](evidence-v0.1-delivery.md) for merge order and PR compare links.

## Known limitations (v0.1 by design)

| Limitation | Notes |
|------------|-------|
| Replay does not invoke `so trace run` | Bundle + `trace_digest` checks only |
| Runtime binding on permit-enforcement emit path only | v0.1; see runtime-evidence-basic guide |
| Live sidecar test requires Linux + CERT-V1 submodule | Skipped on Windows local runs |
| `external/CERT-V1` required for strict cert validation | Clone per `external/README.md` |
| PCS `pf/cmd` test failures | Pre-existing; out of Evidence v0.1 scope |
| Windows testbed | Bash/Git Bash locally; CI uses `ubuntu-latest` |

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
