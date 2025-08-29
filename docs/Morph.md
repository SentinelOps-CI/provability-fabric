## Morph CI: Sharded Lean & Branch-N Replays

This project integrates Morph-based CI pipelines for:

- Sharded Lean builds (snapshotting + shard repro)
- Branch-N parallel replay runs (evidence packs)

### Sharded Lean Builds

Workflow: `.github/workflows/lean-morph.yml`

Configuration:
- Secret `MORPH_API_KEY` enables Morph. Without it, a local sharded fallback runs.
- The workflow first attempts the reusable action `SentinelOps-CI/morph-lean-ci@main`; if unavailable or secret missing, it falls back to local sharded `lake build`.
- Targets: `proofs`, `spec-templates/v1/proofs`, `Fabric.lean`, `Policy.lean`, `ProofBench.lean`.

Snapshot & Repro:
- Morph produces snapshot IDs that allow instant repro of failures from a pre-warmed environment. Snapshot IDs are printed in job logs.

### Branch-N Replay Runner

Workflow: `.github/workflows/morph-replay.yml`

Inputs:
- Zipped bundles from `tests/replay/bundles/*.zip` are generated automatically.
- `branches` (default 8) controls parallel branch count.

Outputs:
- Evidence pack at `evidence/morph/evidence-pack/` (zipped) and `summary.json` with run metadata.

Running Locally:
1) Ensure `MORPH_API_KEY` is available in the CI environment.
2) Trigger the workflow via GitHub Actions (workflow dispatch) and download the artifact `morph-evidence-pack`.

References:
- Morph Lean CI: https://github.com/SentinelOps-CI/morph-lean-ci
- Morph Replay Runner: https://github.com/SentinelOps-CI/morph-replay-runner


