## Summary

Land local audit remediation (36/39 findings DONE, 3 PARTIAL) onto `main` to unblock Wave 7 CI greening. This PR bundles trust-chain hardening, sidecar/ledger burn-down, CI honesty gates, replay submodule fix (F10), and Wave 7 prep documentation.

- **Trust chain (F01–F02, F17, F25):** Cross-language DSSE verify (Go/Rust/TS); fail-closed when `PF_ENFORCE_DSSE=1`; deny-by-default `PF_ENABLED_TOOLS`; evidence hash enforcement.
- **Runtime / ledger (F03–F04, F11, F16, F22, F26–F28):** MCP tenant integration test; 0 production unwrap/expect; 0 ledger `any`; Docker CMD → `dist/index.js`; 23+ Jest tests.
- **CI honesty + Wave 7 prep (F06, F10, F13–F14, F19–F20):** `audit_ci_honesty.py` gate in `ci.yml`; replay Docker contract test; sidecar `integration_tests` with `PF_SHADOW_MODE=1`; `PF_SHADOW_MODE` on paper-conformance; compose smoke in integration workflow.
- **Lean F33:** `Invariants.lean` sorry-free (0 remaining); `generateCertificate` + egress cert lemmas proved.
- **New workflow:** `retrieval-gateway.yml` (F05).

## Pre-merge gates (Linux required)

```bash
bash scripts/linux_validation_checklist.sh
```

| Command | Finding | Local (2026-07-03) |
|---------|---------|-------------------|
| `cargo test -p retrieval-gateway` | F05 | pass (14 tests) |
| `PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests` | F13/F24 | pass (9 tests) |
| `cd runtime/ledger && npm ci && npm test && npm run typecheck:server` | F11/F27 | pass |
| `tests/replay/test_docker_invocation.sh` | F10 | pass on Linux CI (Docker) |
| `python scripts/count_sidecar_unwraps.py --max 10` | F16 | pass (0) |
| `python scripts/count_ledger_any.py --max 20` | F27 | pass (0) |
| `python scripts/audit_ci_honesty.py` | Wave 7 | pass (0 unjustified) |
| `python tests/crypto/test_cross_lang_dsse.py` | F01 | pass |
| `make docs-strict` | F32 | pass |

Windows: Docker replay + compose smoke steps skip without Docker; PR Ubuntu CI is authoritative.

## Submodule (F10)

- `external/TRACE-REPLAY-KIT` @ `957630f1ab8c00031c5f56d32e610a9f8baf69b6`
- `tools/standards/versions.json` pin aligned
- Dockerfile: `ENTRYPOINT ["python", "replay_run.py"]` + `CMD []`

## Post-merge (do not skip)

1. `bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md`
2. Wave 7 clusters per [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md)
3. Target M1: ~20/67 green (replay + security)

## Findings status after merge

| Status | Count | IDs |
|--------|------:|-----|
| DONE (local + awaiting main CI proof) | 36 | F01–F22, F25–F32, F34–F39 |
| PARTIAL | 3 | F23 (Criterion baseline on main), F24 (paper-conformance ×2), F33 (Policy.lean sorries remain) |
| OPEN | 0 | — |

**Not claiming 67/67** until inventory exits 0 twice on `main`.

## Test plan

- [ ] Ubuntu PR CI: `linux_validation_checklist.sh` equivalent jobs green
- [ ] `integration.yaml`: pytest smokes + replay contract + compose smoke
- [ ] `reusable-ci-rust.yml`: `integration_tests` + regression gates
- [ ] `reusable-ci-extended.yml`: `test_cross_lang_dsse.py`
- [ ] `ci.yml`: `audit_ci_honesty.py`
- [ ] `retrieval-gateway.yml`: build + test on path trigger
- [ ] Post-merge: replay cluster ×2, security cluster ×2

## Docs added/updated

- [merge-readiness-checklist.md](merge-readiness-checklist.md)
- [wave7-post-merge-runbook.md](wave7-post-merge-runbook.md)
- [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md)
- [ci-inventory-latest.md](ci-inventory-latest.md)
- [remediation-tracker.md](remediation-tracker.md)
- [ci-health-matrix.md](ci-health-matrix.md)
- [lean-sorry-burn-down.md](lean-sorry-burn-down.md)
- [evidence-program-closure.md](../roadmap/evidence-program-closure.md)

## Risk / split guidance

If review size blocks merge, split into **PR-M0a** (runtime/trust) + **PR-M0b** (CI/workflows); run Linux checklist on each.
