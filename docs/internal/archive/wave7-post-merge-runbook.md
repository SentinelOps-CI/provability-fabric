# Wave 7 post-merge runbook (archived)

> **Historical.** Wave 7 greening narrative and status stamps. Live secret-gated ops:
> [live-ops-secrets.md](../../runbooks/live-ops-secrets.md). Stub at the old path:
> [wave7-post-merge-runbook.md](../wave7-post-merge-runbook.md).

Operational steps to green all **gated** (push/schedule) workflows on `main` after audit remediation merges. Work **one cluster per PR**; mark a cluster DONE only after **two consecutive** successful `main` runs. Honest target after #206: **60/60** gated (not a literal 67/67).

Cluster status: use `gh run list --workflow <file> --branch main --limit 5` (requires `gh`). The former one-shot `scripts/wave7_cluster_status.sh` was removed.

Inventory baseline: [ci-inventory-latest.md](../ci-inventory-latest.md). Cluster map: [ci-health-matrix.md](../ci-health-matrix.md).

---

## Wave 13 — Live ops wiring (secret-gated)

> Prefer the living runbook: [live-ops-secrets.md](../../runbooks/live-ops-secrets.md).

CI-local moto/mock paths remain the **gated push/schedule floor**. Live jobs are **dispatch-only** and **fail closed** when secrets/config are missing (no silent success / greenwash).

### Separation rules

| Workflow | Gated floor (push/PR/schedule) | Live path |
|----------|--------------------------------|-----------|
| `dr-cross.yaml` | `mode=moto` (always on schedule Monday 09:00 UTC) | `workflow_dispatch` `mode=live` |
| `publish-updates.yaml` | dry-run package + HMAC + mock registry | `workflow_dispatch` `dry_run=false` |
| `revocation-sync.yaml` | dry-run mock fetch/merge/sign | `workflow_dispatch` `mode=live` |
| `edge-load.yaml` | smoke against local mock edge | `workflow_dispatch` `mode=full` |

Inventory exit 0 must **not** depend on production AWS or live registries. Adding secrets must not flip the Monday moto schedule into live DR.

### Required secrets

**Live DR (`dr-cross` mode=live)**

| Secret | Purpose |
|--------|---------|
| `AWS_ACCESS_KEY_ID` / `AWS_SECRET_ACCESS_KEY` | AWS API (RDS describe, Route53, S3) |
| `DNS_ZONE_ID` | Route53 hosted zone for `db.provability-fabric.org` |
| `HEALTH_CHECK_ID` | Route53 health check disabled/enabled during failover/recovery |

RDS endpoints are resolved at runtime via `describe-db-instances` (`provability-fabric-primary` / `provability-fabric-secondary`). Sidecar health: `https://sidecar.provability-fabric.org/health`.

**Live registry publish (`publish-updates` dry_run=false)**

| Secret | Purpose |
|--------|---------|
| `UPDATES_REGISTRY_URL` | HTTP PUT endpoint for signed `updates-package.tar.gz` |
| `PUBLISH_UPDATES_SIGNING_KEY` | HMAC key (must not be the CI-local default) |
| `UPDATES_REGISTRY_TOKEN` | Optional bearer token |
| `PUBLISH_UPDATES_METRICS_JSON` | Optional metrics JSON blob when Prometheus is unreachable |

Artifact `package-report.json` must show `live_registry: true`. `docs/updates.md` is updated via **PR** (protected-branch / review policy), not a direct push to `main`.

**Live revocation (`revocation-sync` mode=live)**

| Secret | Purpose |
|--------|---------|
| `REVOCATION_REGISTRY_URL` | External registry JSON URL |
| `REVOCATION_SYNC_SIGNING_KEY` | HMAC signing key for merged list |
| `REVOCATION_REGISTRY_TOKEN` | Optional bearer token |

Produces `revocations.synced.json` + `live-sync-report.json` with `live_registry: true` and opens a review PR.

**Live edge load (`edge-load` mode=full)**

| Secret | Purpose |
|--------|---------|
| `EDGE_REGION_URLS` | Comma-separated region base URLs (>=2 required) |
| `EDGE_LOAD_API_TOKEN` | Optional bearer for admin/purge |

### Dispatch commands

```bash
# Live DR (mutates Route53 health checks when simulate_failover=true)
gh workflow run dr-cross.yaml --ref main -f mode=live -f simulate_failover=true

# Live publish
gh workflow run publish-updates.yaml --ref main -f dry_run=false

# Live revocation sync
gh workflow run revocation-sync.yaml --ref main -f mode=live

# Live edge load
gh workflow run edge-load.yaml --ref main -f mode=full
```

### Success criteria

- Live job run succeeds only with secrets present and real backends reachable.
- Dispatch without secrets exits non-zero (preflight / fail-closed steps).
- Package/sync artifacts label `live_registry=true` or `live_aws=true` / `live_edge=true`.
- Gated moto/mock jobs remain green on push/schedule independently of live secrets.

### Rollback

| Path | Rollback |
|------|----------|
| DR failover | Re-enable primary health check (`aws route53 update-health-check --no-disabled`); confirm DNS returns to primary |
| Publish PR | Close/reject the bot PR; do not merge `docs/updates.md` |
| Revocation PR | Close/reject; do not promote `revocations.synced.json` into `revocations.json` |
| Edge load | Stop the dispatch run; no infra mutation beyond traffic |

---

## Status (2026-07-18 â€” CI-local proofs merged @ `bae36f642`)

**Tip:** `bae36f642` (**PR #223**). Inventory exit **0 Ã—2** â€” **69** gated / **0** red. Replaces secret-absent empty skips with real CI-local proofs (moto DR, mock-registry sync/sign, packaged publish dry-run, multi-region k6 asserts).

| Phase | Status | Evidence |
|-------|--------|----------|
| Wave 7 Phase 3+4 | **DONE** | Historical **60/60** @ `b8b78b94` (below) |
| Wave 8 F33 | **DONE** | MicroInterp `dfa_semantics_match` proved; tracker + reassessment **DONE** |
| Wave 8 re-gates | **DONE** | Prior smokes @ #215â€“#217 |
| lean-offline-full | **DONE** | [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851) |
| CI-local DR (`dr-cross`) | **DONE (CI)** | Tip green [29661142443](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142443) â€” moto S3 CRR + Route53 failover + `blue_green_migrate.sh --dry-run` |
| publish-updates dry-run | **DONE (CI)** | Tip green [29661142449](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142449) â€” package + HMAC + mock-registry |
| revocation-sync dry-run | **DONE (CI)** | Tip green [29661142430](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142430) â€” mock registry merge/sign |
| edge-load / loadtest / perf-proofmeter | **DONE (CI)** | Tip green [29661142462](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142462) / [29661142440](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142440) / [29661142429](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29661142429) |
| Inventory ceremony | **DONE** | Exit **0 Ã—2** @ `bae36f642` â€” **69** gated / **0** red |
| Wave 13 live wiring | **CODE DONE** | Dispatch-only live paths fail-closed; DR live job uses `blue_green_migrate.sh --verify-only`; `--confirm` implements schema+DNS mutation for ops; moto/mock remain gated floor |
| **Next action** | **Ops** | Configure secrets and dispatch live jobs; prove against real backends |

**CI-proven (local/mock; gated):** cross-region DR scripts/terraform surface via moto; publish packaging/signing; revocation sync logic; CI-sized load profiles with hard asserts.

**Live paths wired (fail-closed; need secrets to succeed):** live AWS RDS/Route53/S3 DR (`dr-cross` `mode=live`), live multi-region SaaS edge load (`edge-load` `mode=full`), live registry publish (`publish-updates` `dry_run=false`), live external revocation fetch (`revocation-sync` `mode=live`).

**Dependabot:** deferred (non-trivial Rust/JS bumps and conflict-prone PRs; #152 tiny but red checks).

### Prior status (2026-07-18 â€” Final Wave 7 verification)

**Tip (then):** `6b99ef300` (#221). Inventory exit **0 Ã—2** â€” **69** gated. `lean-offline-full` green [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851).

### Prior status (2026-07-18 â€” Wave 8 lean-offline-full harden)

**Tip (then):** `57664cf03` (#218â€“#220). Full offline green on dispatch [29646806851](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29646806851). F33 / re-gates / tip unblock / lean-offline-full already **DONE**; inventory exit 0 (single pass) before final Ã—2 ceremony.

### Prior status (2026-07-18 â€” Wave 8 revive + tip k6 pin)

**Merged:** **PR #215** (F33 MicroInterp 0 sorry + re-gate 8 leftover smokes) @ `ad4fafd20`. Inventory after tip: **69 gated**, **1 red** (`platform-perf-smoke` â€” unauthenticated GitHub API 403 fetching k6 `releases/latest`). Follow-up pins `K6_VERSION=0.47.0` in `platform-perf-smoke.yml` + `slo-gates.yaml`.

| Phase | Status | Evidence |
|-------|--------|----------|
| Wave 7 Phase 3+4 | **DONE** | Historical **60/60** @ `b8b78b94` (below) |
| Wave 8 F33 | **DONE** | MicroInterp `dfa_semantics_match` proved; lean-style ENFORCED not weakened |
| Wave 8 re-gates | **DONE** | `art-benchmark`, `lean-offline` smoke, `dr-cross` secret-skip, `edge-load`/`loadtest`/`perf-proofmeter`, `publish-updates`/`revocation-sync` green on tip |
| Tip unblock | **DONE** | `platform-perf-smoke` green @ tip after k6 pin ([29638438109](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29638438109)); inventory exit **0** |
| **Next action** | **Optional** | Full SaaS/AWS remain dispatch/live; lean-offline-full moved to schedule+dispatch |

**Still deferred (honest; not demoted â€” live/secret paths):** live AWS DR (`dr-cross` with secrets), multi-region SaaS load, live registry publish, live revocation sync. Smoke/dry-run/skip paths are gated.

### Prior status (2026-07-16 â€” Wave 7 / Phase 3+4 sign-off)

**Merged:** **PR #206** (honest ungate) + **PR #207** (inventory docs). **Main tip:** `b8b78b94`. Inventory **60/60 gated green**, exit **0 Ã—2** (ceremony @ `7d48b3d4` 2026-07-16T20:48Z / 20:50Z; reconfirmed tip 2026-07-16T21:37Z / 21:40Z UTC). Phase 3 hardening proof table below (Phase D).

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 â€” Merge gate | **DONE** | `b8b78b94` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green Ã—2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green Ã—3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **DONE** | Inventory exit 0 Ã—2; tip CI/CodeQL/multiarch/ops-excellence green @ `b8b78b94` ([29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623), [29534144603](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534144603), [29534140842](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534140842), [29534144458](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534144458)) |
| Phase D / Phase 3 | **DONE** | Hardening proof table with run IDs (below) |
| Phase E / Phase 4 | **DONE** | Tracker + closure + reassessment updated; F23/F24 **DONE**; **60/60** Ã—2; ungated list recorded |
| **Next action** | **Optional** | Revive ungated workflows only with real SaaS/AWS smoke |

**Then-honest ungated (superseded by Wave 8 #215):** `dr-cross`, `edge-load`, `loadtest`, `perf-proofmeter`, `publish-updates`, `revocation-sync`, `pf-cross-repo-consumer` (+ prior #194/#196: `lean-offline`, `art-benchmark`).

### Prior status (2026-07-16 â€” Wave 7 / inventory gate closed @ `7d48b3d4`)

**Merged:** **PR #206**. **Main head:** `7d48b3d4`. Inventory **60/60**, exit **0 Ã—2** (2026-07-16T20:48Z / 20:50Z UTC).

### Prior status (2026-07-16 â€” Wave 7 / release + verify-publish + CodeQL)

**Merged:** **PR #204** (release dry-run / missing-`CI_PAT` skip; verify-publish fixture `logs/`; CodeQL JS disk reclaim). **Main head:** `a844d8b0`. Inventory **60/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 â€” Merge gate | **DONE** | `a844d8b0` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green Ã—2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green Ã—3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **IN PROGRESS** | `release.yaml` dry-run green Ã—3 ([29525076387](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525076387)+); `verify-publish-bundle` green Ã—2 ([29525017061](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525017061), [29525078691](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525078691)); `codeql.yaml` green @ tip ([29525017343](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29525017343)); multiarch + ops-excellence green @ tip |
| **Next action** | **7 honest leftovers** | `dr-cross` (AWS creds); skip `disabled_inactivity`: `edge-load` / `loadtest` / `perf-proofmeter` / `publish-updates` / `revocation-sync` / `pf-cross-repo-consumer` unless re-enabled honestly |

### Prior status (2026-07-16 â€” Wave 7 / trust-fire + swebench stress)

**Merged:** **PR #203** (`trust-fire-ga-test` orchestrator smoke; `bench-swebench-stress-scheduled` mock fallback). **Main head:** `00b5257f`. Inventory **54/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 â€” Merge gate | **DONE** | `00b5257f` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green Ã—2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green Ã—3 @ `1ab0d2d5` lineage |
| 1.6 Remaining | **IN PROGRESS** | `trust-fire-ga-test` green [29522471801](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522471801); `bench-swebench-stress-scheduled` green [29522474048](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29522474048); prior: `perf.yaml` / `redteam` green via #200â€“#202 |
| **Next action** | **Next clear gated red** | Prefer `release.yaml` / `verify-publish-bundle.yaml` (`no_run`) or `dr-cross` (needs AWS creds); skip `disabled_inactivity` (`edge-load`/`loadtest`/`perf-proofmeter`/`publish-updates`/`revocation-sync`/`pf-cross-repo-consumer`) unless re-enabled honestly |

### Prior status (2026-07-16 â€” Wave 7 / F23 closeout)

**Merged:** **PR #197** (Criterion CI timeouts/overrides); **PR #198** (ring-buffer MPMC hang). **Main head:** `1ab0d2d5`. Inventory **51/67**.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 â€” Merge gate | **DONE** | `1ab0d2d5` on `main` |
| 1.4 Lean + paper | **DONE (F24)** | `paper-conformance` green Ã—2 @ `f4b0859e` |
| 1.5 Bench + docs | **DONE (F23)** | `bench-nightly-criterion` green Ã—3 @ `1ab0d2d5`: [29508973817](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973817), [29509027731](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509027731), [29509041247](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29509041247) |
| 1.6 Remaining | **IN PROGRESS** | Next clear gated red: `perf.yaml` (confirmed failure); `multiarch-build` tip run in progress |
| **Next action** | **Triage `perf.yaml`** | Last fail [29473421092](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29473421092); watch multiarch [29508973857](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973857) |

### Prior status (2026-07-15 â€” Wave 7 post-merge, session 6)

**Merged:** PR #136 + #144 at `95bcd563`; **PR #146** merged 2026-07-02; **PR #151** at `ee68659c`; **PR #163** (F24 scheduler); **PR #164** (multiarch musl); **PR #176** at `f4b0859e` (paper-conformance geiger drop / F24 closeout). **Main head (then):** `f4b0859e`.

| Phase | Status | Evidence |
|-------|--------|----------|
| 0 â€” Merge gate | **DONE** | `f4b0859e` on `main` |
| 0 â€” PR #146 | **DONE** | Merged 2026-07-02; wasm-scan + CodeQL + retrieval-gateway Docker fixes |
| 1.1 Replay cluster | **GREEN (Ã—1+)** | `platform-replay` [28585705297](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705297), `replay` [28585705517](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705517), `morph-replay` [28585705516](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705516), `platform-cert` [28585705691](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28585705691) |
| 1.2 Security cluster | **GREEN (Ã—1+)** | `scorecards`, `cargo-deny`, `wasm-scan`, `codeql` green on `main` post-#146 |
| 1.3 Platform cluster | **PARTIAL** | `integration` **green** [28639549743](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549743) (F10+F21); **red:** `multiarch-build` [29441338384](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338384) â€” images pushed to GHCR then failed on GHA cache export (transient 400); retry next; `demo-e2e` still red |
| 1.4 Lean + paper | **DONE (F24)** | `lean-style` green; `paper-conformance` green Ã—2 @ `f4b0859e`: [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127); F24 **CLOSED**; integration gates unchanged |
| 1.5 Bench + docs | **PARTIAL** | `docs-build` green; `bench-nightly-criterion` cancelled / needs `refresh_baseline=true` dispatch (F23) |
| 1.6 Remaining | **IN PROGRESS** | Target 69/69 Ã—2; next multiarch retry, then demo-e2e / ops-excellence / billing |
| **Next action** | **Retry multiarch** | `gh workflow run multiarch-build.yaml --ref main` (no code PR until retry confirms non-transient failure) |

### Post-merge commands (run immediately after PR #144 lands)

```bash
# 1. Refresh inventory baseline
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md

# 2. Cluster status (example — repeat per workflow in the cluster map)
gh run list --workflow integration.yaml --branch main --limit 5

# 3. Replay cluster (M1) â€” watch first main runs
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

## B.1 Replay cluster (5 workflows) â€” F10 main proof

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

## B.2 Security cluster â€” F20 main proof

| Workflow | Likely fix |
|----------|------------|
| `codeql.yaml` | Artifact upload chain (matrix fix landed locally) |
| `cargo-deny.yml` | `deny.toml` / feature flags |
| `wasm-scan.yaml` | Empty-registry skip or registry config |
| `scorecards.yml` | Regression guard â€” keep green |

**Exit:** CodeQL + cargo-deny green twice (scorecards already green on `main`).

---

## B.3 Platform cluster â€” F06/F12/F19 main proof

| Workflow | Local fix |
|----------|-----------|
| `slo-gates.yaml` | Mock PF server + lockfile (F19) |
| `integration.yaml` | F06 smokes + replay contract + `test_ledger_mcp_tenant.py` + compose smoke |
| `operational-excellence.yaml` | Real `tests/integration/test_*.py` paths |
| `demo-e2e.yml` | `run-demo.ts` (F07/F18) |
| `billing-test.yaml` | Ledger gates (`typecheck:server`, `--max 20`) |

**Exit:** â‰¥4/5 platform workflows green twice.

---

## B.4 Lean + paper-conformance â€” F24 main proof

| Workflow | Notes |
|----------|-------|
| `paper-conformance.yaml` | **GREEN Ã—2** â€” F24 CLOSED; runs [29441338434](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29441338434), [29443718127](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29443718127) on `f4b0859e` (PR #176); `PF_SHADOW_MODE=1` on integration + rate-limits |
| `lean-offline.yaml` | Mathlib cache paths aligned with `lean-style.yaml` |
| `lean-style.yaml` | Enforced sorry-free targets only â€” green |
| `lean-morph.yml` | Optional `MORPH_API_KEY` |

**Exit (met):** `paper-conformance.yaml` green twice on `main`; `lean-style.yaml` green on enforced targets. Integration gates unchanged.

---

## B.5 Bench + docs â€” F23/F32 main proof

| Workflow | Action |
|----------|--------|
| `bench-nightly-criterion.yaml` | `workflow_dispatch` with `refresh_baseline: true` per repo `bench/BASELINE.md` |
| `performance-gate.yaml` | Align thresholds post-baseline |
| `docs-build.yaml`, `docs-deploy.yaml` | `make docs-strict` on Linux CI |

**Exit:** Criterion + docs-build green twice; F23 â†’ **DONE**.

---

## B.6 Remaining ~30 workflows (M3 â†’ M5)

Weekly triage:

```bash
bash scripts/ci_workflow_inventory.sh --markdown > docs/internal/ci-inventory-latest.md
diff docs/internal/ci-inventory-latest.md   # vs prior week
```

**Priority after clusters:**

1. `retrieval-gateway.yml`
2. `docker-compose-*` / compose smoke paths
3. `marketplace-e2e.yaml`
4. DR / automation workflows (`dr-cross.yaml`, `trust-fire-ga-test.yaml`, â€¦)

**Process:** one workflow per PR until:

```bash
bash scripts/ci_workflow_inventory.sh   # exit 0
bash scripts/ci_workflow_inventory.sh   # second consecutive exit 0
```

**Exit:** inventory exits 0 twice (all remaining push/schedule workflows green). Achieved 2026-07-16 @ `7d48b3d4` as **60/60** after honest ungating of seven SaaS/AWS leftovers (historical target label was 67/67).

---

## Phase D â€” Production hardening proof (post-merge) â€” **DONE**

| ID | Hardening | Wired in CI | Main proof (run IDs) |
|----|-----------|-------------|----------------------|
| F01 | Cross-lang DSSE | `ci.yml` â†’ `reusable-ci-extended.yml` â†’ `tests/crypto/test_cross_lang_dsse.py` | Green: [29534141623](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29534141623) (`b8b78b94`, log: `cross-lang DSSE tests passed`); [29529736631](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29529736631) (`7d48b3d4`) |
| F02 | Deny-by-default tools | Compose `PF_ENABLED_TOOLS=` + in-tree `env_config::enabled_tools_deny_by_default` | Compose empty allow-list exercised by `docker-compose-smoke.sh full` in `integration.yaml` [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) + [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636). Unit test is in-tree; `reusable-ci-rust.yml` curated suite does **not** run sidecar `--lib` (hang avoidance) |
| F03/F04 | Ledger MCP tenant | `integration.yaml` â†’ `tests/integration/test_ledger_mcp_tenant.py` | Green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) (4 tenant tests passed); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |
| F05 | retrieval-gateway | `retrieval-gateway.yml` | Green Ã—2+: [29410389588](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29410389588), [28639549745](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/28639549745) |
| F21 | Compose smoke | `integration.yaml` â†’ `scripts/docker-compose-smoke.sh full` | Green: [29508973757](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29508973757) (`=== docker-compose smoke passed ===`); [29489277636](https://github.com/SentinelOps-CI/provability-fabric/actions/runs/29489277636) |

---

## Phase E â€” Sign-off ceremony â€” **DONE** (2026-07-16)

Inventory exit 0 Ã—2 achieved (2026-07-16 @ `7d48b3d4`, **60/60** gated; tip `b8b78b94` after #207). Do **not** claim literal 67/67.

```bash
bash scripts/ci_workflow_inventory.sh
bash scripts/ci_workflow_inventory.sh
bash scripts/linux_validation_checklist.sh
python scripts/audit_ci_honesty.py
python scripts/count_sidecar_unwraps.py --max 10
python scripts/count_ledger_any.py --max 20
```

Updated: [remediation-tracker.md](remediation-tracker.md), [evidence-program-closure.md](../roadmap/evidence-program-closure.md), [archive/full-repo-audit-reassessment-2026-07-03.md](archive/full-repo-audit-reassessment-2026-07-03.md).
