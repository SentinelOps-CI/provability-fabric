# GitHub Actions workflow map

High-level grouping of files under `.github/workflows/`. Open each file for exact `on:` triggers.

## Core CI

- **ci.yml** — Main PR/push CI: Buf lint, path filter, reusable prepare / Lean / Rust / Go-Node / extended.
- **ci-weekly-full.yml** — Scheduled full matrix plus Buf (catches drift when PRs used doc-only skips).
- **ci-nightly-pytest.yml** — Nightly Python/integration/red-team sweep.
- **reusable-ci-prepare.yml** — Gates, impacted selection, DSSE fixture test.
- **reusable-ci-lean.yml** — Elan + `lean-toolchain`, Lake builds, Lean gates, proofbench.
- **reusable-ci-rust.yml** — `cargo build` / `test` / `clippy` workspace and sidecar lib tests.
- **reusable-ci-go-node.yml** — Spectral, Go CLI/admission, ledger/SDK tests, console/demo builds, `services/*` Go build.
- **reusable-ci-extended.yml** — Red-team, k6 smoke, integration pytest, optional cosign on push.

## Security and compliance

codeql.yaml, scorecards.yml (OpenSSF Scorecard), sbom-diff.yaml, release-sbom.yml (CycloneDX on GitHub Release), **dependency-review.yml** (vulnerable deps + license policy on PRs), **cargo-deny.yml** (Rust licenses / advisories / `deny.toml`), **actionlint.yml** (workflow YAML static checks), wasm-scan.yaml, proto-compat.yaml, compliance.yaml, privacy-test.yaml, operational-excellence.yaml, redteam.yaml, trust-fire-ga-test.yaml, jwks-validate.yml, cert-validate.yml, platform-cert-validate.yml, revocation-sync.yaml, allowlist-sync.yaml.

## Lean, proofs, policy

lean-morph.yml, lean-offline.yaml, lean-style.yaml, morph-replay.yml, nightly-replay.yml, replay.yml, platform-replay.yml, policy-build.yml, policy-gates.yaml, policy-pr-proof.yml, proof-bot.yaml, proof-fuzz.yaml, paper-conformance.yaml, dfa.yaml, spec-ai.yaml, standards-pin.yml.

## Benchmarks and performance

bench-nightly-criterion.yaml, bench-swebench-smoke.yaml, bench-swebench-stress-scheduled.yaml, bench-swebench-unit.yaml, perf.yaml, performance-gate.yaml, perf-proofmeter.yaml, platform-perf-smoke.yml, art-benchmark.yaml, loadtest.yaml, edge-load.yaml.

## Platform, adapters, demos

adapters-ci.yml, integration.yaml, demo-e2e.yml, marketplace-e2e.yaml, egress.yml, pf-ci.yaml, pf-reusable-caller.yaml, pf-cross-repo-consumer.yaml, publish-updates.yaml, release.yaml, multiarch-build.yaml, docs-build.yaml, docs-deploy.yaml.

## Misc automation

pr-comments.yml, cla-bot.yaml, bundle-check.yaml, dep-graph.yaml, verify-publish-bundle.yaml, fuzz.yaml, heartbeat-test.yaml, incident-e2e.yaml, incident-test.yaml, opa-test.yaml, rbac-test.yaml, billing-test.yaml, slo-gates.yaml, dr-cross.yaml, chaos-nightly.yaml.

## Maintenance

When adding a workflow, add a one-line note in the appropriate section above so others can discover it without scanning the directory.

## External standards checkout

Workflows that validate CERT-V1, run TRACE-REPLAY-KIT replay, or link-check docs against
`external/` paths must initialize standards explicitly:

```yaml
- uses: actions/checkout@v4
- name: Init external standards
  env:
    STANDARDS_GITHUB_TOKEN: ${{ secrets.STANDARDS_GITHUB_TOKEN }}
  run: make submodules
```

Do **not** use `actions/checkout` with `submodules: true` or `submodules: recursive` — the
repo vendors Lean mathlib separately via `make vendor-mathlib`, and private upstream
standards require `STANDARDS_GITHUB_TOKEN` (see [`tools/standards/README.md`](../tools/standards/README.md)).

| Pattern | When |
|---------|------|
| Plain `actions/checkout@v4` | No CERT-V1/KIT dependency (demo-e2e, policy-build, most Rust/Go CI) |
| Checkout + `make submodules` | cert-validate, replay, egress, platform-replay, platform-cert-validate, nightly-replay, evidence-v01-smoke, docs-build, standards-pin |
| Checkout + `make vendor-mathlib` | Lean offline / reusable-ci-lean when `vendor/mathlib` is not cached |
