# Evidence v0.1 status

Completion checklist for the Evidence v0.1 workstream.

| Item | Status |
|------|--------|
| Schemas (`specs/evidence/v0.1/schemas/`) | Complete |
| Public spec docs | Complete |
| Fixtures + compatibility matrix | Complete |
| `pf evidence bundle pack` | Complete |
| `pf evidence validate --strict` | Complete |
| `pf evidence replay` | Complete |
| Runtime binding (`evidence_v01_binding`) | Complete |
| Examples (`evidence-basic`, `runtime-evidence-basic`, `forensic-replay-basic`) | Complete |
| Testbed scripts + CI smoke | Complete |
| Quickstart + CHANGELOG | Complete |

## Verification commands

```bash
go test ./...   # in core/evidence
go build -o pf . # in core/cli/pf
./pf evidence validate specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json --strict
pytest tests/evidence_schema tests/evidence_validation tests/evidence_replay -q
bash testbed/evidence-v0.1/run_happy_path.sh
```

## Out of scope (v0.1)

- Replacing PCS `EvidenceBundle.v0` admission
- Replacing `so bundle pack` spec tar archives
- Redefining CERT-V1 schema (external standard only)
