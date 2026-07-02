# Merge Readiness Checklist (Phase 0)

Prerequisite for landing local audit remediation onto `main`. **Do not merge** until every gate below passes on an Ubuntu runner (local WSL or CI on the merge PR).

Source: [Audit Remediation Program](../roadmap/evidence-program-closure.md), reassessment [full-repo-audit-reassessment-2026-07-02.md](./full-repo-audit-reassessment-2026-07-02.md).

Last verified: **2026-07-03** (local Windows prep; Linux Docker/replay authoritative on PR CI).

## Pre-merge (local / PR branch)

- [x] Resolve merge conflicts with `main` (branch `audit-remediation-merge` rebased/current)
- [x] Open merge PR(s); request review — [PR #144](https://github.com/SentinelOps-CI/provability-fabric/pull/144)
- [x] Submodule `external/TRACE-REPLAY-KIT` at pinned commit with Dockerfile `CMD []` (F10) — `957630f`
- [x] Run Linux validation script (Windows: skip Docker/replay; see notes below):

```bash
bash scripts/linux_validation_checklist.sh
```

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
make no-runtime-placeholders
make docs-strict
```

**Windows local results (2026-07-03):**

| Command | Exit | Notes |
|---------|------|-------|
| `cargo test -p retrieval-gateway` | 0 | 14 tests |
| `PF_SHADOW_MODE=1 cargo test -p sidecar-watcher --test integration_tests` | 0 | 9 tests |
| `cd runtime/ledger && npm test && npm run typecheck:server` | 0 | 23 passed, 1 skipped |
| `tests/replay/test_docker_invocation.sh` | skip | Docker not available on Windows |
| `python scripts/count_sidecar_unwraps.py --max 10` | 0 | 0 unwraps |
| `python scripts/count_ledger_any.py --max 20` | 0 | 0 `any` |
| `python scripts/audit_ci_honesty.py` | 0 | 0 unjustified |
| `python tests/crypto/test_cross_lang_dsse.py` | 0 | cross-lang DSSE |
| `make no-runtime-placeholders` | 0 | |
| `make docs-strict` | 0 | after internal doc link fixes |

## Submodule bump (F10)

- [x] `tools/standards/versions.json` pin matches `external/TRACE-REPLAY-KIT` HEAD (`957630f1ab8c00031c5f56d32e610a9f8baf69b6`)
- [x] `external/TRACE-REPLAY-KIT/runner/Dockerfile` uses `ENTRYPOINT ["python", "replay_run.py"]` and `CMD []`
- [ ] `tests/replay/test_docker_invocation.sh` exits 0 on Linux CI (`platform-replay.yml` or `integration.yaml`) — **pending PR Ubuntu run**

## CI wiring verified on PR

- [x] `platform-replay.yml` — replay docker contract test step wired
- [x] `integration.yaml` — replay contract test step + `test_ledger_mcp_tenant.py` + compose smoke
- [x] `reusable-ci-rust.yml` — `integration_tests` + regression gates + `retrieval-gateway`
- [x] `reusable-ci-extended.yml` — `test_cross_lang_dsse.py` (F01)
- [x] `ci.yml` — `audit_ci_honesty.py` gate
- [x] `retrieval-gateway.yml` — build + test on path trigger (F05)
- [x] Placeholder gate: `make no-runtime-placeholders` exit 0 (excludes `build/`, `dist/`, binaries)
- [x] `replay.yml` — F10 docker contract test added (preemptive Wave 7 triage)

## Post-merge (main — do NOT skip)

- [x] Refresh CI inventory baseline (2026-07-03; `main` still 12/68 green until merge):

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
```

- [ ] Two consecutive green runs on replay cluster (5 workflows)
- [ ] Two consecutive green runs on security cluster (CodeQL, cargo-deny)
- [ ] Update [remediation-tracker.md](./remediation-tracker.md) and [evidence-program-closure.md](../roadmap/evidence-program-closure.md)

## Explicit non-actions (per program)

- **No force-merge to `main`** without green Linux gates above
- **No weakening** Lean enforced sorry set or vacuous test gates
- **No `passWithNoTests`** in required marketplace workflow

## Target milestone M1

~20/67 gated workflows green after replay + security clusters unlock.

## Merge approval

**Merge to `main` requires explicit user approval** after PR #144 Linux CI gates pass.
