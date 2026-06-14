# External dependencies (git submodules)

Pinned standards live under `external/` as git submodules. Tags are locked in
[`tools/standards/versions.json`](../tools/standards/versions.json).

| Submodule | Repository | Purpose |
|-----------|------------|---------|
| `CERT-V1/` | [verifiable-ai-ci/CERT-V1](https://github.com/verifiable-ai-ci/CERT-V1) | CERT-V1 JSON schema and validation |
| `TRACE-REPLAY-KIT/` | [verifiable-ai-ci/TRACE-REPLAY-KIT](https://github.com/verifiable-ai-ci/TRACE-REPLAY-KIT) | Deterministic trace replay runner |

## Fresh clone

```bash
git clone https://github.com/SentinelOps-CI/provability-fabric.git
cd provability-fabric
make dev-standards
```

`make submodules` runs [`scripts/init_external_standards.sh`](../scripts/init_external_standards.sh),
which checks out pinned commits from [`tools/standards/versions.json`](../tools/standards/versions.json).

### CI and private upstream repos

`verifiable-ai-ci/CERT-V1` and `verifiable-ai-ci/TRACE-REPLAY-KIT` are private. GitHub Actions
must set repository secret **`STANDARDS_GITHUB_TOKEN`**: a fine-grained or classic PAT with
`repo` read access to those repositories. The Evidence smoke workflow passes this secret to
`make submodules`.

If you already cloned without submodules:

```bash
make submodules
make standards-pin-check
```

## Docker Compose

`docker-compose.yml` mounts these directories for evidence-service and replay-service.
If submodules are missing, Compose creates empty mount points; run `make submodules`
before relying on CERT validation or deep replay.

## Windows / Docker

For local Windows development without native submodule paths, mount this repo into
Docker Compose and run sidecar or cert tests inside the Linux container where
`external/CERT-V1` is available.
