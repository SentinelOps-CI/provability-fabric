# Wave 7 post-merge runbook

Operational steps to green **67/67** gated workflows on `main` after audit remediation merges. Work **one cluster per PR**; mark a cluster DONE only after **two consecutive** successful `main` runs.

Helper: `bash scripts/wave7_cluster_status.sh` (requires `gh`).

Inventory baseline: [ci-inventory-latest.md](ci-inventory-latest.md). Cluster map: [ci-health-matrix.md](ci-health-matrix.md).

---

## Status (2026-07-15 — Wave 7 post-merge, session 5)

**Merged:** PR #136 + #144 at `95bcd563`; **PR #146** merged 2026-07-02 (wasm-scan, retrieval-gateway Docker, CodeQL); **PR #151** at `ee68659c` (F21 compose postgres init, 2026-07-03). **Main head:** `ee68659c` (no push since 2026-07-03).

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `ee68659c` on `main` |
| 0 — PR #146 | **DONE** | Merged 2026-07-02; wasm-scan + CodeQL + retrieval-gateway Docker fixes |
| 1.1 Replay cluster | **GREEN (×1+)** | `platform-replay` [28585705297](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297), `replay` [28585705517](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517), `morph-replay` [28585705516](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516), `platform-cert` [28585705691](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691) |
| 1.2 Security cluster | **GREEN (×1+)** | `scorecards`, `cargo-deny`, `wasm-scan`, `codeql` green on `main` post-#146 |
| 1.3 Platform cluster | **PARTIAL** | `integration` **green** [28639549743](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549743) (F10+F21); **red:** `multiarch-build` [28639549827](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549827) — fix in [PR #164](https://github.com/SentinelOps-CI/provability-fabric/pull/164); `demo-e2e` still red |
| 1.4 Lean + paper | **IN PROGRESS** | `lean-style` green; `paper-conformance` red [29389589027](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29389589027) (scheduler heap ordering) — fix in [PR #163](https://github.com/SentinelOps-CI/provability-fabric/pull/163) |
| 1.5 Bench + docs | **PARTIAL** | `docs-build` green; `bench-nightly-criterion` needs `refresh_baseline=true` dispatch (F23) |
| 1.6 Remaining | **IN PROGRESS** | Honest inventory **38/69** green (2026-07-15); target 69/69 ×2 |
| **Active PRs** | **#163, #164** | Scheduler priority fix (F24); native musl multiarch Docker build |

### Post-merge commands (run immediately after PR #144 lands)

```bash
# 1. Refresh inventory baseline
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md

# 2. Cluster status helper
bash scripts/wave7_cluster_status.sh

# 3. Replay cluster (M1) — watch first main runs
gh run list --workflow platform-replay.yml --branch main --limit 5
gh run list --workflow replay.yml --branch main --limit 5

# 4. Security cluster
gh run list --workflow codeql.yaml --branch main --limit 5
gh run list --workflow cargo-deny.yml --branch main --limit 5

# 5. Platform cluster
gh run list --workflow integration.yaml --branch main --limit 5
gh run list --workflow slo-gates.yaml --branch main --limit 5

# 6. Lean + paper (M2)
gh run list --workflow paper-conformance.yaml --branch main --limit 5
gh run list --workflow lean-style.yaml --branch main --limit 5

# 7. Bench baseline refresh (M4)
gh workflow run bench-nightly-criterion.yaml --ref main -f refresh_baseline=true

# 8. Triage failures
gh run view <run-id> --log-failed
```

---

## Prerequisites (Phase A complete)

1. Merge PR **audit-remediation-merge** to `main` (no force-push).
2. On Ubuntu (PR CI or WSL):

```bash
bash scripts/linux_validation_checklist.sh
```

3. Refresh inventory:

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
```

**Target M1:** ~20/67 green after replay + security clusters unlock.

---

## B.1 Replay cluster (5 workflows) — F10 main proof

| Workflow | Triage command |
|----------|----------------|
| `platform-replay.yml` | `gh run view --log-failed` |
| `nightly-replay.yml` | same |
| `platform-cert-validate.yml` | same |
| `replay.yml` | same |
| `morph-replay.yml` | same |

**Steps:**

1. Confirm submodule `external/TRACE-REPLAY-KIT` @ `957630f` matches `tools/standards/versions.json`.
2. Confirm Docker passes `python replay_run.py` args (not `bash replay_run.sh` as Python arg).
3. Local contract: `bash tests/replay/test_docker_invocation.sh` (wired in `integration.yaml` + replay workflows).
4. Fix workflow drift; open **PR-C1** if post-merge failures differ from local.
5. **Exit:** all 5 workflows green **twice** on `main`.

---

## B.2 Security cluster — F20 main proof

| Workflow | Likely fix |
|----------|------------|
| `codeql.yaml` | Artifact upload chain (matrix fix landed locally) |
| `cargo-deny.yml` | `deny.toml` / feature flags |
| `wasm-scan.yaml` | Empty-registry skip or registry config |
| `scorecards.yml` | Regression guard — keep green |

**Exit:** CodeQL + cargo-deny green twice (scorecards already green on `main`).

---

## B.3 Platform cluster — F06/F12/F19 main proof

| Workflow | Local fix |
|----------|-----------|
| `slo-gates.yaml` | Mock PF server + lockfile (F19) |
| `integration.yaml` | F06 smokes + replay contract + `test_ledger_mcp_tenant.py` + compose smoke |
| `operational-excellence.yaml` | Real `tests/integration/test_*.py` paths |
| `demo-e2e.yml` | `run-demo.ts` (F07/F18) |
| `billing-test.yaml` | Ledger gates (`typecheck:server`, `--max 20`) |

**Exit:** ≥4/5 platform workflows green twice.

---

## B.4 Lean + paper-conformance — F24 main proof

| Workflow | Notes |
|----------|-------|
| `paper-conformance.yaml` | `PF_SHADOW_MODE=1` on integration + rate-limits jobs |
| `lean-offline.yaml` | Mathlib cache paths aligned with `lean-style.yaml` |
| `lean-style.yaml` | Enforced sorry-free targets only |
| `lean-morph.yml` | Optional `MORPH_API_KEY` |

**Steps:**

1. Watch first `paper-conformance.yaml` run post-merge.
2. Triage mathlib vendor/cache if `lean-offline.yaml` fails.
3. **Exit:** `paper-conformance.yaml` green twice; `lean-style.yaml` green on enforced targets.

---

## B.5 Bench + docs — F23/F32 main proof

| Workflow | Action |
|----------|--------|
| `bench-nightly-criterion.yaml` | `workflow_dispatch` with `refresh_baseline: true` per repo `bench/BASELINE.md` |
| `performance-gate.yaml` | Align thresholds post-baseline |
| `docs-build.yaml`, `docs-deploy.yaml` | `make docs-strict` on Linux CI |

**Exit:** Criterion + docs-build green twice; F23 → **DONE**.

---

## B.6 Remaining ~30 workflows (M3 → M5)

Weekly triage:

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
diff docs/internal/ci-inventory-latest.md   # vs prior week
```

**Priority after clusters:**

1. `retrieval-gateway.yml`
2. `docker-compose-*` / compose smoke paths
3. `marketplace-e2e.yaml`
4. DR / automation workflows (`dr-cross.yaml`, `trust-fire-ga-test.yaml`, …)

**Process:** one workflow per PR until:

```bash
bash scripts/ci_workflow_inventory.sh   # exit 0
bash scripts/ci_workflow_inventory.sh   # second consecutive exit 0
```

**Exit:** 67/67 gated workflows green twice.

---

## Phase D — Production hardening proof (post-merge)

| ID | Proof on `main` |
|----|-----------------|
| F01 DSSE | `tests/crypto/test_cross_lang_dsse.py` in `reusable-ci-extended.yml` |
| F02 deny-by-default tools | `env_config::enabled_tools_deny_by_default` unit test + compose `PF_ENABLED_TOOLS=` |
| F03/F04 MCP tenant | `tests/integration/test_ledger_mcp_tenant.py` in `integration.yaml` |
| F05 retrieval-gateway | `retrieval-gateway.yml` green twice |
| F21 compose smoke | `scripts/docker-compose-smoke.sh` in `integration.yaml` |

---

## Phase E — Sign-off ceremony

When 67/67 achieved:

```bash
bash scripts/ci_workflow_inventory.sh
bash scripts/ci_workflow_inventory.sh
bash scripts/linux_validation_checklist.sh
python scripts/audit_ci_honesty.py
python scripts/count_sidecar_unwraps.py --max 10
python scripts/count_ledger_any.py --max 20
```

Update [remediation-tracker.md](remediation-tracker.md), [evidence-program-closure.md](../roadmap/evidence-program-closure.md), and publish [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md).
