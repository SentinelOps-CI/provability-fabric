# Wave 7 post-merge runbook

Operational steps to green all **gated** (push/schedule) workflows on `main` after audit remediation merges. Work **one cluster per PR**; mark a cluster DONE only after **two consecutive** successful `main` runs. Honest target after #206: **60/60** gated (not a literal 67/67).

Helper: `bash scripts/wave7_cluster_status.sh` (requires `gh`).

Inventory baseline: [ci-inventory-latest.md](ci-inventory-latest.md). Cluster map: [ci-health-matrix.md](ci-health-matrix.md).

---

## Status (2026-07-18 — Final Wave 7 verification)

**Tip:** `6b99ef300` (#221 lean-offline-full sign-off; harden lineage #218–#220). Inventory exit **0 ×2** on `main` (2026-07-18T15:02Z / 15:04Z UTC): **69** gated, **0** red. `lean-offline-full` green [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851).

| Phase | Status | Evidence |
|-------|--------|----------|
| Wave 7 Phase 3+4 | **DONE** | Historical **60/60** @ `b8b78b94` (below) |
| Wave 8 F33 | **DONE** | MicroInterp `dfa_semantics_match` proved; tracker + reassessment **DONE** |
| Wave 8 re-gates | **DONE** | `art-benchmark`, `lean-offline` smoke, `dr-cross` secret-skip, `edge-load`/`loadtest`/`perf-proofmeter`, `publish-updates`/`revocation-sync` green on tip |
| Tip unblock | **DONE** | `platform-perf-smoke` green @ tip after k6 pin ([29638438109](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29638438109)) |
| lean-offline-full | **DONE** | Tip proof [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851) (~5m): shared lean-style cache, vendor, lake update, iptables DROP, offline lake build; Monday schedule + dispatch |
| Inventory ceremony | **DONE** | Exit **0 ×2** @ tip `6b99ef300` — **69** gated / **0** red |
| **Next action** | **Optional** | Live SaaS/AWS remain secret/live-mode only |

**Still deferred (honest; not demoted):** live AWS DR (`dr-cross` with secrets), multi-region SaaS load, live registry publish, live revocation sync. Smoke/dry-run/secret-skip paths stay gated and do not claim live proof. `lean-offline-full` is no longer dispatch-only — it also runs on the Monday schedule.

### Prior status (2026-07-18 — Wave 8 lean-offline-full harden)

**Tip (then):** `57664cf03` (#218–#220). Full offline green on dispatch [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851). F33 / re-gates / tip unblock / lean-offline-full already **DONE**; inventory exit 0 (single pass) before final ×2 ceremony.

### Prior status (2026-07-18 — Wave 8 revive + tip k6 pin)

**Merged:** **PR #215** (F33 MicroInterp 0 sorry + re-gate 8 leftover smokes) @ `ad4fafd20`. Inventory after tip: **69 gated**, **1 red** (`platform-perf-smoke` — unauthenticated GitHub API 403 fetching k6 `releases/latest`). Follow-up pins `K6_VERSION=0.47.0` in `platform-perf-smoke.yml` + `slo-gates.yaml`.

| Phase | Status | Evidence |
|-------|--------|----------|
| Wave 7 Phase 3+4 | **DONE** | Historical **60/60** @ `b8b78b94` (below) |
| Wave 8 F33 | **DONE** | MicroInterp `dfa_semantics_match` proved; lean-style ENFORCED not weakened |
| Wave 8 re-gates | **DONE** | `art-benchmark`, `lean-offline` smoke, `dr-cross` secret-skip, `edge-load`/`loadtest`/`perf-proofmeter`, `publish-updates`/`revocation-sync` green on tip |
| Tip unblock | **DONE** | `platform-perf-smoke` green @ tip after k6 pin ([29638438109](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29638438109)); inventory exit **0** |
| **Next action** | **Optional** | Full SaaS/AWS remain dispatch/live; lean-offline-full moved to schedule+dispatch |

**Still deferred (honest; not demoted — live/secret paths):** live AWS DR (`dr-cross` with secrets), multi-region SaaS load, live registry publish, live revocation sync. Smoke/dry-run/skip paths are gated.

### Prior status (2026-07-16 — Wave 7 / Phase 3+4 sign-off)

**Merged:** **PR #206** (honest ungate) + **PR #207** (inventory docs). **Main tip:** `b8b78b94`. Inventory **60/60 gated green**, exit **0 ×2** (ceremony @ `7d48b3d4` 2026-07-16T20:48Z / 20:50Z; reconfirmed tip 2026-07-16T21:37Z / 21:40Z UTC). Phase 3 hardening proof table below (Phase D).

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `b8b78b94` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green ×2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green ×3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **DONE** | Inventory exit 0 ×2; tip CI/CodeQL/multiarch/ops-excellence green @ `b8b78b94` ([29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623), [29534144603](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534144603), [29534140842](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534140842), [29534144458](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534144458)) |
| Phase D / Phase 3 | **DONE** | Hardening proof table with run IDs (below) |
| Phase E / Phase 4 | **DONE** | Tracker + closure + reassessment updated; F23/F24 **DONE**; **60/60** ×2; ungated list recorded |
| **Next action** | **Optional** | Revive ungated workflows only with real SaaS/AWS smoke |

**Then-honest ungated (superseded by Wave 8 #215):** `dr-cross`, `edge-load`, `loadtest`, `perf-proofmeter`, `publish-updates`, `revocation-sync`, `pf-cross-repo-consumer` (+ prior #194/#196: `lean-offline`, `art-benchmark`).

### Prior status (2026-07-16 — Wave 7 / inventory gate closed @ `7d48b3d4`)

**Merged:** **PR #206**. **Main head:** `7d48b3d4`. Inventory **60/60**, exit **0 ×2** (2026-07-16T20:48Z / 20:50Z UTC).

### Prior status (2026-07-16 — Wave 7 / release + verify-publish + CodeQL)

**Merged:** **PR #204** (release dry-run / missing-`CI_PAT` skip; verify-publish fixture `logs/`; CodeQL JS disk reclaim). **Main head:** `a844d8b0`. Inventory **60/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `a844d8b0` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green ×2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green ×3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **IN PROGRESS** | `release.yaml` dry-run green ×3 ([29525076387](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525076387)+); `verify-publish-bundle` green ×2 ([29525017061](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525017061), [29525078691](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525078691)); `codeql.yaml` green @ tip ([29525017343](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525017343)); multiarch + ops-excellence green @ tip |
| **Next action** | **7 honest leftovers** | `dr-cross` (AWS creds); skip `disabled_inactivity`: `edge-load` / `loadtest` / `perf-proofmeter` / `publish-updates` / `revocation-sync` / `pf-cross-repo-consumer` unless re-enabled honestly |

### Prior status (2026-07-16 — Wave 7 / trust-fire + swebench stress)

**Merged:** **PR #203** (`trust-fire-ga-test` orchestrator smoke; `bench-swebench-stress-scheduled` mock fallback). **Main head:** `00b5257f`. Inventory **54/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `00b5257f` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green ×2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green ×3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **IN PROGRESS** | `trust-fire-ga-test` green [29522471801](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522471801); `bench-swebench-stress-scheduled` green [29522474048](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522474048); prior: `perf.yaml` / `redteam` green via #200–#202 |
| **Next action** | **Next clear gated red** | Prefer `release.yaml` / `verify-publish-bundle.yaml` (`no_run`) or `dr-cross` (needs AWS creds); skip `disabled_inactivity` (`edge-load`/`loadtest`/`perf-proofmeter`/`publish-updates`/`revocation-sync`/`pf-cross-repo-consumer`) unless re-enabled honestly |

### Prior status (2026-07-16 — Wave 7 / F23 closeout)

**Merged:** **PR #197** (Criterion CI timeouts/overrides); **PR #198** (ring-buffer MPMC hang). **Main head:** `1ab0d2d5`. Inventory **51/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `1ab0d2d5` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green ×2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green ×3 @ `1ab0d2d5`: [29508973817](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973817), [29509027731](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509027731), [29509041247](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509041247) |
| 1.6 Remaining | **IN PROGRESS** | Next clear gated red: `perf.yaml` (confirmed failure); `multiarch-build` tip run in progress |
| **Next action** | **Triage `perf.yaml`** | Last fail [29473421092](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29473421092); watch multiarch [29508973857](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973857) |

### Prior status (2026-07-15 — Wave 7 post-merge, session 6)

**Merged:** PR #136 + #144 at `95bcd563`; **PR #146** merged 2026-07-02; **PR #151** at `ee68659c`; **PR #163** (F24 scheduler); **PR #164** (multiarch musl); **PR #176** at `f4b0859e` (paper-conformance geiger drop / F24 closeout). **Main head (then):** `f4b0859e`.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 — Merge gate | **DONE** | `f4b0859e` on `main` |
| 0 — PR #146 | **DONE** | Merged 2026-07-02; wasm-scan + CodeQL + retrieval-gateway Docker fixes |
| 1.1 Replay cluster | **GREEN (×1+)** | `platform-replay` [28585705297](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297), `replay` [28585705517](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517), `morph-replay` [28585705516](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516), `platform-cert` [28585705691](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691) |
| 1.2 Security cluster | **GREEN (×1+)** | `scorecards`, `cargo-deny`, `wasm-scan`, `codeql` green on `main` post-#146 |
| 1.3 Platform cluster | **PARTIAL** | `integration` **green** [28639549743](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549743) (F10+F21); **red:** `multiarch-build` [29441338384](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338384) — images pushed to GHCR then failed on GHA cache export (transient 400); retry next; `demo-e2e` still red |
| 1.4 Lean + paper | **DONE (F24)** | `lean-style` green; `paper-conformance` green ×2 @ `f4b0859e`: [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127); F24 **CLOSED**; integration gates unchanged |
| 1.5 Bench + docs | **PARTIAL** | `docs-build` green; `bench-nightly-criterion` cancelled / needs `refresh_baseline=true` dispatch (F23) |
| 1.6 Remaining | **IN PROGRESS** | Target 69/69 ×2; next multiarch retry, then demo-e2e / ops-excellence / billing |
| **Next action** | **Retry multiarch** | `gh workflow run multiarch-build.yaml --ref main` (no code PR until retry confirms non-transient failure) |

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
| `paper-conformance.yaml` | **GREEN ×2** — F24 CLOSED; runs [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127) on `f4b0859e` (PR #176); `PF_SHADOW_MODE=1` on integration + rate-limits |
| `lean-offline.yaml` | Mathlib cache paths aligned with `lean-style.yaml` |
| `lean-style.yaml` | Enforced sorry-free targets only — green |
| `lean-morph.yml` | Optional `MORPH_API_KEY` |

**Exit (met):** `paper-conformance.yaml` green twice on `main`; `lean-style.yaml` green on enforced targets. Integration gates unchanged.

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

**Exit:** inventory exits 0 twice (all remaining push/schedule workflows green). Achieved 2026-07-16 @ `7d48b3d4` as **60/60** after honest ungating of seven SaaS/AWS leftovers (historical target label was 67/67).

---

## Phase D — Production hardening proof (post-merge) — **DONE**

| ID | Hardening | Wired in CI | Main proof (run IDs) |
|----|-----------|-------------|----------------------|
| F01 | Cross-lang DSSE | `ci.yml` → `reusable-ci-extended.yml` → `tests/crypto/test_cross_lang_dsse.py` | Green: [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623) (`b8b78b94`, log: `cross-lang DSSE tests passed`); [29529736631](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29529736631) (`7d48b3d4`) |
| F02 | Deny-by-default tools | Compose `PF_ENABLED_TOOLS=` + in-tree `env_config::enabled_tools_deny_by_default` | Compose empty allow-list exercised by `docker-compose-smoke.sh full` in `integration.yaml` [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) + [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636). Unit test is in-tree; `reusable-ci-rust.yml` curated suite does **not** run sidecar `--lib` (hang avoidance) |
| F03/F04 | Ledger MCP tenant | `integration.yaml` → `tests/integration/test_ledger_mcp_tenant.py` | Green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) (4 tenant tests passed); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F05 | retrieval-gateway | `retrieval-gateway.yml` | Green ×2+: [29410389588](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588), [28639549745](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549745) |
| F21 | Compose smoke | `integration.yaml` → `scripts/docker-compose-smoke.sh full` | Green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) (`=== docker-compose smoke passed ===`); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |

---

## Phase E — Sign-off ceremony — **DONE** (2026-07-16)

Inventory exit 0 ×2 achieved (2026-07-16 @ `7d48b3d4`, **60/60** gated; tip `b8b78b94` after #207). Do **not** claim literal 67/67.

```bash
bash scripts/ci_workflow_inventory.sh
bash scripts/ci_workflow_inventory.sh
bash scripts/linux_validation_checklist.sh
python scripts/audit_ci_honesty.py
python scripts/count_sidecar_unwraps.py --max 10
python scripts/count_ledger_any.py --max 20
```

Updated: [remediation-tracker.md](remediation-tracker.md), [evidence-program-closure.md](../roadmap/evidence-program-closure.md), [full-repo-audit-reassessment-2026-07-03.md](full-repo-audit-reassessment-2026-07-03.md).
