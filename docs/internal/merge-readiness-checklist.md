# Merge Readiness Checklist (Phase 0)

Prerequisite for landing local audit remediation onto `main`. **Do not merge** until every gate below passes on an Ubuntu runner (local WSL or CI on the merge PR).

Source: [Audit Remediation Program](../roadmap/evidence-program-closure.md), reassessment [full-repo-audit-reassessment-2026-07-03.md](./full-repo-audit-reassessment-2026-07-03.md).

## Pre-merge (local / PR branch)

- [x] Branch `audit-remediation-merge` prepared with staged remediation
- [ ] Resolve merge conflicts with `main` (rebase/merge at PR time)
- [x] Open merge PR(s); PR body at [merge-pr-body.md](./merge-pr-body.md)
- [x] Submodule `external/TRACE-REPLAY-KIT` at pinned commit with Dockerfile `CMD []` (F10)
- [x] Run Linux validation script (Windows: all except Docker steps):

```bash
bash scripts/linux_validation_checklist.sh
```

**Local verification (2026-07-03, Windows):**

| Step | Exit | Notes |
|------|------|-------|
| `cargo test -p retrieval-gateway` | 0 | 14 tests |
| `PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests` | 0 | 9 tests |
| `cd runtime/ledger && npm test && npm run typecheck:server` | 0 | 23 passed, 1 skipped |
| `tests/replay/test_docker_invocation.sh` | skip | Docker not on Windows dev host |
| `python scripts/count_sidecar_unwraps.py --max 10` | 0 | 0 unwrap/expect |
| `python scripts/count_ledger_any.py --max 20` | 0 | 0 `any` |
| `python scripts/audit_ci_honesty.py` | 0 | 56 justified, 0 unjustified |
| `python tests/crypto/test_cross_lang_dsse.py` | 0 | cross-lang DSSE |
| `make docs-strict` | 0 | mkdocs strict |

Equivalent manual commands:

```bash
cargo test -p retrieval-gateway
PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests
cd runtime/ledger && npm ci && npm test && npm run typecheck:server
tests/replay/test_docker_invocation.sh   # requires Docker + submodule
python scripts/count_sidecar_unwraps.py --max 10
python scripts/count_ledger_any.py --max 20
python scripts/audit_ci_honesty.py
python tests/crypto/test_cross_lang_dsse.py
make docs-strict
```

## Submodule bump (F10)

- [x] `tools/standards/versions.json` pin matches `external/TRACE-REPLAY-KIT` HEAD (`957630f`)
- [x] `external/TRACE-REPLAY-KIT/runner/Dockerfile` uses `ENTRYPOINT ["python", "replay_run.py"]` and `CMD []`
- [ ] `tests/replay/test_docker_invocation.sh` exits 0 on Linux CI (`platform-replay.yml` or `integration.yaml`) — pending PR CI

## CI wiring verified on PR

- [x] `platform-replay.yml` — replay docker contract test step
- [x] `integration.yaml` — replay contract + compose smoke + MCP tenant pytest
- [x] `reusable-ci-rust.yml` — `integration_tests` + regression gates
- [x] `reusable-ci-extended.yml` — `test_cross_lang_dsse.py`
- [x] `ci.yml` — `audit_ci_honesty.py` gate
- [x] `retrieval-gateway.yml` — build + test (F05)
- [x] Placeholder gate: `make no-runtime-placeholders` exit 0 (excludes `build/`, `dist/`, binaries)

## Post-merge (main — do NOT skip)

- [x] Refresh CI inventory baseline (generated 2026-07-03; reflects **pre-merge** `main` at 13/68 green):

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
```

- [ ] Two consecutive green runs on replay cluster (5 workflows)
- [ ] Two consecutive green runs on security cluster (CodeQL, cargo-deny)
- [ ] Update [remediation-tracker.md](./remediation-tracker.md) and [evidence-program-closure.md](../roadmap/evidence-program-closure.md) when 67/67 achieved

## Explicit non-actions (per program)

- **No force-merge to `main`** without green Linux gates above
- **No weakening** Lean enforced sorry set or vacuous test gates
- **No `passWithNoTests`** in required marketplace workflow

## Target milestone M1

~20/67 gated workflows green after replay + security clusters unlock. Runbook: [wave7-post-merge-runbook.md](./wave7-post-merge-runbook.md).
