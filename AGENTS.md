# Agent and contributor guide

This file orients humans and automation to how the repository is built, what must never be committed, and where CI lives.

## Do not commit

- `node_modules/` under any package (e.g. `runtime/ledger`, `marketplace/ui`, `console`). Run `npm ci` locally. For the ledger, run `npx prisma generate` after install; see [runtime/ledger/README.md](runtime/ledger/README.md).
- Rust `target/` (already in `.gitignore`).
- Local SWE-bench trees: `workspaces/`, `bench/swebench/workspaces/` (ignored at repo root to avoid accidental adds).
- Local SWE-bench harness outputs under `runs/`, repo-root `predictions*.jsonl`, `.venv/` / `.venv-wsl/`, and stray files named like `--flag-name` (see [.gitignore](.gitignore)).

## Public PR checklist (before push)

- Confirm **no secrets** in commits or the PR diff: API keys, tokens, `sk-` / `pit_` literals, private URLs, pasted `env.json` or `.env` contents.
- **Files changed** on GitHub: skim for unexpected paths (`runs/`, `node_modules/`, local fixtures). Never commit `node_modules/`; use `npm ci` per package.
- If you ever committed credentials, **rotate** them; use `git filter-repo` only with maintainer coordination (see [SECURITY.md](SECURITY.md)).

## Primary CI entry

- [.github/workflows/ci.yml](.github/workflows/ci.yml) is the main pipeline for `push` / `pull_request` to `main`.
- It always runs **protobuf** lint (`api/` via Buf) and a **path filter**: pull requests that touch only `docs/**` or `figs/**` skip the heavy jobs; **pushes to `main` always run the full matrix**.
- Reusable pieces live under `.github/workflows/reusable-ci-*.yml` (prepare, Lean, Rust, Go/Node, extended tests).
- [.github/workflows/ci-weekly-full.yml](.github/workflows/ci-weekly-full.yml) runs on a weekly schedule plus `workflow_dispatch` to catch drift when PRs used doc-only skips.
- [.github/workflows/ci-nightly-pytest.yml](.github/workflows/ci-nightly-pytest.yml) runs a broader Python/integration sweep nightly.

## Local commands (minimal)

- Rust workspace: `cargo build --workspace`, `cargo test --workspace --exclude sidecar-watcher`, `cargo test -p sidecar-watcher --lib`, `cargo test -p sidecar-watcher --tests`, `cargo clippy --workspace -- -D warnings`. Policy and advisories: install [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) and run `cargo deny check` (see [deny.toml](deny.toml)). See `runtime/sidecar-watcher/tests/README.md` for quarantined integration sources.
- Lean: toolchain pin is in [lean-toolchain](lean-toolchain); use `lake build` from the relevant `lakefile.lean` directory (see CI reusable Lean workflow for order). Elan installer in CI/devcontainer is pinned to tag **v4.2.1** (bump in `.github/workflows/reusable-ci-lean.yml` and `.devcontainer/devcontainer.json` together).
- Docs: root [mkdocs.yml](mkdocs.yml) builds to **`./build`** (not `site`). Use `pip install -r docs/requirements.txt` then `mkdocs build` from the repo root.
- Platform: see [Makefile](Makefile) and [README.md](README.md) for Docker Compose targets.

## Dependency updates

- [`.github/dependabot.yml`](.github/dependabot.yml) covers Cargo, GitHub Actions, selected npm roots, and Go modules.

## Security and supply chain

- Vulnerability reporting: [SECURITY.md](SECURITY.md).
- OpenSSF Scorecard: [.github/workflows/scorecards.yml](.github/workflows/scorecards.yml) (scheduled + on push to `main`).
- SBOM and Grype gate: [.github/workflows/sbom-diff.yaml](.github/workflows/sbom-diff.yaml) (pinned Syft/Grype release archives, not `curl | sh` installers).
- Published releases: CycloneDX JSON is attached by [.github/workflows/release-sbom.yml](.github/workflows/release-sbom.yml).
- Pull requests: [.github/workflows/dependency-review.yml](.github/workflows/dependency-review.yml) flags high-or-worse vulnerable dependency changes and blocks strong copyleft licenses (requires dependency graph enabled on the repo).
- Workflow YAML: [.github/workflows/actionlint.yml](.github/workflows/actionlint.yml) runs [actionlint](https://github.com/rhysd/actionlint) when `.github/workflows/**` changes.

## Workflow inventory

- See [.github/WORKFLOWS.md](.github/WORKFLOWS.md) for a grouped list of workflow files and their roles.
- Human-readable CI and supply-chain summary: [docs/reference/ci-reference.md](docs/reference/ci-reference.md).

## PF CI upstream checkout

- [.github/workflows/pf-ci.yaml](.github/workflows/pf-ci.yaml) checks out `SentinelOps-CI/provability-fabric` into `ci-src/` so shared CI scripts stay aligned with the reference repo; use `CI_PAT` when `GITHUB_TOKEN` cannot read that repository.
