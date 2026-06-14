# Continuous integration reference

This page summarizes GitHub Actions for this repository: the **main CI entry**, **supply-chain and workflow-quality gates**, **reusable language jobs**, and specialized pipelines (bench, PF CI, Helm).

## Main CI (`ci.yml`)

- **Triggers:** `push` and `pull_request` to `main`.
- **Protobuf:** Buf lint on `api/`.
- **Path filter:** Pull requests that touch only `docs/**` or `figs/**` skip heavy jobs; **pushes to `main` always run the full matrix** (see workflow `paths-ignore` rules).
- **Reusable workflows:** `.github/workflows/reusable-ci-prepare.yml`, `reusable-ci-lean.yml`, `reusable-ci-rust.yml`, `reusable-ci-go-node.yml`, `reusable-ci-extended.yml`.
- **Rust (reusable-ci-rust):** Workspace `cargo build`, `cargo test`, `cargo clippy`. The `sidecar-watcher` crate uses `autotests = false`; CI runs `cargo test -p sidecar-watcher --lib` and `cargo test -p sidecar-watcher --tests` for explicit `[[test]]` targets only. See `runtime/sidecar-watcher/tests/README.md` for quarantined integration sources.
- **Broader schedules:** `.github/workflows/ci-weekly-full.yml` (weekly full matrix + Buf), `.github/workflows/ci-nightly-pytest.yml` (nightly Python/integration sweep).

## Supply chain and workflow hygiene

| Workflow | Role |
|----------|------|
| `dependency-review.yml` | On PRs: blocks introduction of dependencies with **high (or worse)** known vulnerabilities; **denies** selected strong-copyleft licenses. Requires the repository [dependency graph](https://docs.github.com/en/code-security/supply-chain-security/understanding-your-software-supply-chain/about-the-dependency-graph) where applicable. |
| `cargo-deny.yml` | Runs [`cargo deny`](https://github.com/EmbarkStudios/cargo-deny) `check` against the workspace using root **`deny.toml`** (licenses, RustSec advisories, duplicate-crate warnings). |
| `actionlint.yml` | When `.github/workflows/**` changes: lints workflow YAML via Docker image **`rhysd/actionlint:1.7.12`**. |
| `sbom-diff.yaml` | SBOM generation/diff and Grype-style checks (pinned Syft/Grype installers). |
| `release-sbom.yml` | On `release: published`, attaches CycloneDX JSON to the GitHub Release. |
| `scorecards.yml` | [OpenSSF Scorecard](https://scorecard.dev/) on a schedule and on pushes to `main`. |

Contributor-oriented pointers: **[CONTRIBUTING.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/CONTRIBUTING.md)** (local commands, what not to commit) and **[.github/WORKFLOWS.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/WORKFLOWS.md)** (workflow inventory).

---

## PF CI reusable workflow (TRUST-FIRE)

The sections below document the reusable PF CI workflow that runs TRUST-FIRE GA phases, builds runtime images, and validates results, plus related bench and Helm material.

## Workflows

### Bench SWE-bench Smoke (`.github/workflows/bench-swebench-smoke.yaml`)

- **Purpose**: Lightweight PR gate and smoke for the SWE-bench pipeline. No network, no model keys, no Docker.
- **Triggers**: Every pull request; push to `main`/`master` when paths under `bench/swebench/`, `bench/fixtures/`, `tests/test_swebench_runner_smoke.py`, or this workflow change; schedule (nightly); `workflow_dispatch`.
- **Job `bench-smoke`**: Installs pytest and runs `pytest tests/test_swebench_runner_smoke.py -q --tb=short`. Uses mock engine and local fixtures; no HuggingFace or OpenHands. Runs on any OS (Windows/Linux/macOS). Full bench with OpenHands and harness evaluation require Linux or WSL.
- **Job `rust-tests`**: Optional (`continue-on-error: true`). Runs `cargo test -q --workspace --no-fail-fast`. Uses the shared `.github/actions/cache-cargo` composite for cargo cache. Criterion benchmarks are not run on PRs.
- **Job `nightly-with-model`**: Optional; runs only when the `BENCH_SWEBENCH_NIGHTLY_TOKEN` secret is set (schedule or workflow_dispatch). Runs the same smoke tests; can be extended for full bench with model/dataset.

### Bench SWE-bench unit (`.github/workflows/bench-swebench-unit.yaml`)

- **Purpose**: Regression tests for experiments scripts and bench/swebench components using synthetic fixtures (no Docker, no OpenHands, no HuggingFace network).
- **Triggers**: Push and pull_request to `main` when paths under `bench/swebench/**`, `experiments/**`, `tests/test_*.py`, or `tests/fixtures/**` change.
- **Job `pytest`**: Matrix `ubuntu-latest`, `windows-latest`. Installs pytest and runs the module list in `.github/workflows/bench-swebench-unit.yaml` (Step "Run bench/swebench and experiments unit tests"), including: `test_experiments_compare_runs`, `test_validate_predictions`, `test_check_no_stub`, `test_validate_pf_run`, `test_loader_from_file`, `test_workspace_plan`, `test_replay_roundtrip` (skipped on Windows), `test_swebench_runner_smoke`, `test_openhands_engine`, `test_policy_loader`, `test_cost_report`, `test_proof_hook`, `test_check_wsl_env`, `test_fill_manifest_from_run`, `test_list_delta_cases`, `test_bucket_pf_failures`, `test_policy_guard_deny_allow`, **`test_provider_env`**, **`test_openhands_provider_env`**, **`test_run_swebench_eval_cleanup`**, **`test_run_config`** (provider routing, compare strict gates, eval cleanup scoping, `RunConfig` defaults). Additional tests in `tests/test_*.py` (e.g. `test_runner_core`, `test_summarize_stress_run`, modular SWE-bench component tests) may be run locally; see `docs/guides/testing-guide.md` and `docs/internal/swebench-stabilization-regression-matrix.md`.

### Bench Nightly Criterion (`.github/workflows/bench-nightly-criterion.yaml`)

- **Purpose**: Criterion performance baseline and regression check (aligned with `bench/README.md`). Smoke job runs on PRs; save/compare run on push or schedule.
- **Triggers**: Push to `main`/`master` when `bench/`, `runtime/sidecar-watcher/`, or Cargo files change; pull_request when same paths change; schedule (cron 0 2 * * *); `workflow_dispatch`.
- **Job `smoke-bench`**: On push or PR, runs `cargo criterion -p provability-fabric-bench -- --sample-size 5 --noplot` to ensure benches compile and run; no regression gate.
- **Cargo cache**: Jobs use the shared `.github/actions/cache-cargo` composite (with `key-suffix: "-criterion-deps"`). Criterion baseline is cached separately in `target/criterion`.
- **Job `save-baseline`**: On push to main, runs `cargo bench -p provability-fabric-bench -- --save-baseline main` and caches `target/criterion`.
- **Job `compare-baseline`**: On schedule, restores cached baseline and runs `cargo bench -p provability-fabric-bench -- --baseline main`; fails if regression exceeds threshold.

**Local baseline:** Run `make bench-save-baseline` to save the Criterion baseline and write `bench/BASELINE.md` (date, git_sha, machine). See `bench/README.md` for the notice that numeric thresholds are targets until baselines are recorded.

**Rust perf policy:** Criterion save/compare run in nightly or `workflow_dispatch`; PRs run only the smoke-bench job. Baselines are stored as workflow cache (`target/criterion`). For local runs, use `cargo bench -p provability-fabric-bench -- --baseline main` to compare against the saved baseline; run `cargo bench` to regenerate HTML reports under `target/criterion/` (cargo-criterion does not support baseline or HTML options).

### Bench SWE-bench stress scheduled (`.github/workflows/bench-swebench-stress-scheduled.yaml`)

- **Purpose**: Weekly run of `exp-step2-lite-stress-large-repos` (heavy-repo slice). Not gated in CI; produces trend artifacts.
- **Triggers**: Schedule (cron 0 3 * * 0, Sunday 03:00); `workflow_dispatch`.
- **Job `stress-run`**: Runs on `ubuntu-latest`, long timeout. Fills manifest, runs baseline and PF-guarded runs for the stress instance set, runs harness and compare, then **`experiments/scripts/summarize_stress_run.py`** to write **stress_summary.json** (schema_version, pf_commit, agent_commit, dataset_id, dataset_version, harness_id; timeout_rate_*, wall_clock_s_median/p95, guard_overhead_s_median, empty_patch_reasons_topN, solve rates). **Stress regression alerts** step runs **`experiments/scripts/check_stress_alerts.py`**; thresholds are read from **experiments/config/stress_alerts.yaml** (optional; script uses built-in defaults if missing). Fails the job when parity, timeout delta, empty_patch rate, or guard_overhead exceed thresholds. Uploads compare.json, stress_summary.json, compare.csv; uploads **stress_summary.json** as named artifact **stress-summary**.

### Verify publish bundle (`.github/workflows/verify-publish-bundle.yaml`)

- **Purpose**: Sanity check that the publish-bundle verifier and fixture are valid (no network, no Docker). Runs unit tests for publish_docs and the verifier against the fixture so changes to publish_docs or publish_bundle are regression-tested.
- **Triggers**: Push (main/master) and pull_request when `experiments/scripts/verify_publish_bundle.py`, `experiments/scripts/publish_docs.py`, `experiments/scripts/publish_bundle.py`, `experiments/scripts/export_publish_artifacts.py`, `experiments/scripts/update_run_ids_if_green.py`, `experiments/fixtures/verify_publish_bundle/**`, `experiments/schemas/compare_report.schema.json`, `tests/test_publish_docs.py`, `tests/test_verify_publish_bundle_fixture.py`, or this workflow change; `workflow_dispatch`.
- **Job `verify`**: (1) Install pytest; (2) run `pytest tests/test_publish_docs.py tests/test_verify_publish_bundle_fixture.py -v`; (3) run `python experiments/scripts/verify_publish_bundle.py --publish-dir experiments/fixtures/verify_publish_bundle/publish --compare-json experiments/fixtures/verify_publish_bundle/compare.json --skip-run-dir-check`.
- **After pushing**: Confirm the "Verify publish bundle" workflow is green in the Actions tab when any of the triggered paths change.

### PF CI (reusable)

- Local reusable workflow: `.github/workflows/pf-ci.yaml`

## What it does

- Installs toolchains (Python 3.11, Go 1.23, Rust stable)
- Installs Kind, kubectl, and Helm
- Builds and loads images for:
  - `runtime/sidecar-watcher`
  - `runtime/admission-controller`
  - `runtime/ledger`
  - `runtime/attestor`
  - Note: `runtime/wasm-sandbox` and the Rust adapters (`adapters/http-get`, `adapters/file-read`) are not built as Docker images in this workflow; add them to the workflow if needed for deployment.
- Runs TRUST-FIRE GA subset (phases 2, 3, and 6 by default)
- Fails the job unless `trust-fire-report.json` contains `overall_status: PASS`

## Inputs

- `pr_number` (string, optional): PR number (for callers that need it)
- `run_phases` (string, optional, default `"2,3,6"`): Comma-separated phases to run
- `kind_cluster_name` (string, optional, default `"pf-ci"`): Kind cluster name

## Secrets

- `GITHUB_TOKEN` (optional): Used by some TRUST-FIRE steps
- `CI_PAT` (optional): PAT for cross-repo checkout, if needed

## Example usage (local)

```yaml
name: PF Reusable CI Caller
on:
  pull_request:
  schedule:
    - cron: "0 3 * * *"
jobs:
  call-pf-ci:
    uses: ./.github/workflows/pf-ci.yaml
    with:
      pr_number: ${{ github.event.pull_request.number || '' }}
      run_phases: "2,3,6"
    secrets:
      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

## Cross-repo usage

Publish the reusable workflow to a central repository (e.g., `org/ci-workflows`) under `.github/workflows/pf-ci.yaml` and tag a version (e.g., `v1`). Then call it:

```yaml
name: Cross-Repo PF CI Consumer
on:
  pull_request:
  schedule:
    - cron: "0 3 * * *"
jobs:
  pf-ci:
    uses: org/ci-workflows/.github/workflows/pf-ci.yaml@v1
    with:
      pr_number: ${{ github.event.pull_request.number || '' }}
      run_phases: "2,3,6"
    secrets:
      GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

---

# Helm Chart: pf-enforce

**Path**: `charts/pf-enforce`

## Components
- MutatingWebhookConfiguration: Injects `sidecar-watcher` into pods labeled `pf/enforce=true`
- ValidatingWebhookConfiguration: Blocks pods lacking a valid PAB signature
- Admission controller Deployment + Service (HTTPS 8443)
- RBAC & ServiceAccount
- Sidecar ConfigMap (default sidecar JSON)

## Values

```yaml
image:
  sidecarWatcher:
    repository: provability-fabric/sidecar-watcher
    tag: latest
    pullPolicy: IfNotPresent
  admissionController:
    repository: provability-fabric/admission-controller
    tag: latest
    pullPolicy: IfNotPresent

webhooks:
  namespaceSelector: {}
  objectSelector:
    matchExpressions:
      - key: pf/enforce
        operator: In
        values: ["true"]
  timeouts:
    mutating: 10
    validating: 10
  failurePolicy: Fail

caBundle: ""

admission:
  replicaCount: 1
  service:
    type: ClusterIP
    port: 443
  tls:
    secretName: pf-enforce-certs
```

## Install

```bash
helm install pf-enforce charts/pf-enforce \
  --set caBundle=$(kubectl get cm -n kube-system extension-apiserver-authentication -o jsonpath='{.data.client-ca-file}' | base64 -w0)
```

Adjust `caBundle` to match your cluster’s CA.

---

# Makefile: PAB Signing Targets

Targets added:

- `pf-sign`: cosign keyless sign `bundles/<SERVICE_NAME>/bundle.json` and record `sigstore_digest`

```bash
make pf-sign SERVICE_NAME=my-service
```

- `pf-verify`: verify signature and run `pf verify`

```bash
make pf-verify SERVICE_NAME=my-service
```

---

# Service Bootstrap Template

**Path**: `templates/pf-bootstrap/pf.yaml`

Example:

```yaml
service: <service-name>
attestor:
  endpoint: http://attestor-service:8080
ledger:
  endpoint: http://ledger-service:4000
redis:
  url: redis://redis-master:6379

tools:
  http_fetch:
    allowlist:
      - https://api.example.com
      - https://*.trusted.com
```

Use as a starting point for new service repos.

