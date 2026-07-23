# Engineering latency budgets (Wave E5)

Non-Lean engineering speed budgets for local launch and CI path-awareness.
Out of scope: Lean/mathlib wall-clock (see [lean-build.md](../dev/lean-build.md)).

**North-star (Wave E plan):** docs-only gated push **&lt;5 min**; sidecar-only PR skips Go/Node/console installs; warm `make ledger-up` **&lt;60s** to healthy GraphQL; CI honesty unchanged (`scripts/audit_ci_honesty.py` → 0 unjustified).

---

## Budgets

| Scenario | Budget | What counts | Notes |
|----------|--------|-------------|-------|
| Docs-only push to `main` | **&lt;5 min** gated wall-clock | Jobs that still run after path-filter (honesty / Buf / prepare when required; **not** Rust/Go-Node/extended/Lean language matrices) | Changes under only `docs/**` or `figs/**` must skip language slices via `ci.yml` `dorny/paths-filter` |
| Sidecar-only PR | Rust touched crates only; **no** Go/Node console `npm ci` | `reusable-ci-rust.yml` impacted selection; `reusable-ci-go-node.yml` path-scoped jobs | Touching `runtime/sidecar-watcher/**` + crates must not activate console workspace |
| Warm `make ledger-up` | **&lt;60s** to `http://localhost:4000/health` | From `make ledger-up` return with images already present; health via `docker compose up --wait` | Cold `--build` / first pull **excluded**; use `platform-up-build` when rebuild is intentional |
| `make compose-smoke` (local, warm images) | **&lt;3 min** | `scripts/check_wiring.py` + compose config + `up --wait` for smoke services + health curls + `down` | Cold image build/pull **excluded** from this budget |
| Wiring check alone | **&lt;15s** | `python scripts/check_wiring.py` / `make check-wiring` | No Docker required |
| CI `engineering-budget-smoke` (schedule) | Wiring **&lt;30s**; compose-smoke **&lt;15 min** | Same scripts on `ubuntu-latest` | GHA cold pulls inflate compose wall-clock; see cache-warm note below |

---

## How to measure

### Docs-only gated push

1. Push a commit that touches only `docs/**` (or open a docs-only PR and compare the `changes` job outputs).
2. In Actions, open the `CI` workflow run → confirm `ci-rust` / `ci-go-node` / `ci-extended` / Lean language jobs are **skipped**.
3. Sum wall-clock of jobs that actually ran (typically honesty + path filter + any always-on prepare steps that still apply). Target **&lt;5 min**.
4. Cross-check: weekly [`ci-weekly-full.yml`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/ci-weekly-full.yml) still exercises the full matrix on a schedule (honesty: path skip ≠ “never tested”).

```bash
# Local approximation of the filter (no Actions):
git diff --name-only origin/main...HEAD
# Expect only docs/** or figs/** for a docs-only claim.
```

### Sidecar-only PR

1. Open a PR that changes only sidecar / Rust paths under the `rust` filter (no `runtime/ledger/**`, `console/**`, Go modules).
2. Confirm `reusable-ci-go-node` console job skipped; Rust runs impacted crates (`tools/select_impacted_rust.py`), not a blind full-workspace tax on every crate.
3. Record install steps: no console `npm ci`.

### Warm `make ledger-up`

```bash
# Prerequisite: images already built (prior platform-up / ledger-up / compose pull).
make demo-down 2>/dev/null || docker compose --profile ledger down -v 2>/dev/null || true
/usr/bin/time -p make ledger-up
curl -fsS http://localhost:4000/health
```

On Windows PowerShell:

```powershell
Measure-Command { make ledger-up }
Invoke-WebRequest -Uri http://localhost:4000/health -UseBasicParsing
```

Do **not** include `make platform-up-build` or first-time image builds in the &lt;60s claim.

### Compose-smoke / wiring

```bash
/usr/bin/time -p make check-wiring
/usr/bin/time -p make compose-smoke
```

Scheduled CI mirror: [`engineering-budget-smoke.yml`](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/engineering-budget-smoke.yml) times both and fails with an explicit over-budget message.

---

## Cache-warm note (CI vs local)

| Environment | Expectation |
|-------------|-------------|
| Local warm | Docker images present; compose does not `--build`; health-wait only |
| Local cold | First pull/build unbounded relative to budgets above — warm then re-measure |
| GitHub Actions schedule | Runner may have empty image cache; **compose-smoke CI budget (15 min)** absorbs cold pulls. Wiring budget stays tight. Over-budget fail messages must state whether the step was wiring or compose-smoke |

Do not treat a cold GHA compose wall-clock as a regression of the local **&lt;60s ledger-up** or **&lt;3 min warm compose-smoke** budgets.

---

## What Wave E1–E4 changed (latency-relevant)

| Wave | Change | Latency / cost effect |
|------|--------|------------------------|
| **E1** | `make platform-up` / `ledger-up` / `enforcement-up` / `full-up` / `compose-smoke`; `docker compose up --wait`; no fixed `sleep 30`; `PROFILE=dev` ledger; [local-workflows.md](../dev/local-workflows.md); just wrappers | Local happy path stops waiting a fixed 30s and stops rebuilding by default |
| **E2** | Port/URL alignment; `scripts/check_wiring.py`; MCP keep-alive; prod fail-closed; warm tool-broker; `schemas/pf-env.schema.json`; SDK HTTP/`/health` cleanup | Fewer miswired retries; less cold TCP on MCP checks; faster “launch then discover env” failure |
| **E3.1** | `ci.yml` path-condition on **push** symmetric to PR | Docs-only / slice-only pushes skip non-impacted language jobs → docs-only &lt;5 min gated target |
| **E3.2–E3.3** | Split `reusable-ci-rust` (impacted + nextest) and `reusable-ci-go-node` (parallel go-cli/ledger/sdk/pcs; path-scoped console); root npm workspaces | Sidecar-only and package-scoped PRs pay less install/test tax |
| **E3.4–E3.5** | CodeQL/ops/scorecard/schema schedule or path-filter; inventory + [ci-reference.md](../reference/ci-reference.md) honesty | Always-on burners no longer tax every push; inventory ≠ “every workflow every tip” |
| **E4** | Composite actions (`setup-node-workspace`, `setup-go-cli`, `setup-python-tests`); `scripts/go-work-init.sh`; path-aware `make install-dev`; Kind path-gate in `integration.yaml`; extended pytest non-Kind default | Less setup duplication; Kind only when admission/helm paths change; compose-smoke remains default integration signal |

**Preserved (do not regress):** Wave 11 multiarch path filters, Criterion smoke-vs-schedule split, paper-conformance path/shard, CI honesty gate.

---

## Related

- Launch matrix: [local-workflows.md](../dev/local-workflows.md)
- CI path behavior: [ci-reference.md](../reference/ci-reference.md)
- Tracker before/after: [remediation-tracker.md](remediation-tracker.md) § Wave E
- Schedule guard: `.github/workflows/engineering-budget-smoke.yml`
