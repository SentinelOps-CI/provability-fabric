## Standards & Sources of Truth

This repository consumes external standards as read-only sources of truth via git submodules under `external/`.

- CERT-V1 (schema + verifiers): https://github.com/verifiable-ai-ci/CERT-V1
- TRACE-REPLAY-KIT (runner + oracles): https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT

Integration demos and tooling:
- morph-lean-ci (sharded Lean CI): https://github.com/SentinelOps-CI/morph-lean-ci
- morph-replay-runner (branch-N replays): https://github.com/SentinelOps-CI/morph-replay-runner
- mcp-sidecar-demo (permissions/epochs/IFC): https://github.com/SentinelOps-CI/mcp-sidecar-demo

We do not copy schemas into this repository. Instead, validation tools reference the schema directly from the submodule path `external/CERT-V1/schema/cert-v1.schema.json`.

See `tools/cert-validate/README.md` for validating local certificates and `.github/workflows/cert-validate.yml` for CI validation.


