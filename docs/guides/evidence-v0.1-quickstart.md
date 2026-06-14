# Evidence v0.1 quickstart

Get from clone to validated bundle in a few commands.

## Prerequisites

- Go 1.23+
- Python 3.10+ with `jsonschema` and `pytest` for tests
- Repository root as working directory
- External standards: `git clone --recurse-submodules …` or `make dev-standards` after clone

## Steps

```bash
# 1. Build CLI
cd core/cli/pf && go build -o pf . && cd ../../..

# 2. Validate checked-in fixture
./core/cli/pf/pf evidence validate \
  specs/evidence/v0.1/examples/valid/basic-evidence-bundle.json --strict

# 3. Pack from manifest
./core/cli/pf/pf evidence bundle pack \
  --manifest examples/evidence-basic/manifest.json \
  --out /tmp/evidence-bundle.json

# 4. Replay check
./core/cli/pf/pf evidence replay --bundle /tmp/evidence-bundle.json --out /tmp/replay.json
```

## Evidence v0.2 (opt-in)

```bash
make dev-standards   # CERT-V1 + TRACE-REPLAY-KIT submodules

# Import KIT trace → v0.1 execution-trace artifact
./core/cli/pf/pf evidence trace import \
  --kit-trace tests/replay/bundles/simple/trace.json \
  --out /tmp/execution-trace.json

# Pack / validate v0.2 bundle with replay_context (see specs/evidence/v0.2/examples/valid/)
./core/cli/pf/pf evidence validate \
  specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --strict --base-dir specs/evidence/v0.2/examples/valid

# Deep replay (requires KIT submodule + Python deps from runner/requirements.txt)
./core/cli/pf/pf evidence replay \
  --bundle specs/evidence/v0.2/examples/valid/deep-replay-bundle.json \
  --base-dir specs/evidence/v0.2/examples/valid \
  --execute --low-view
```

Before `cargo test -p sidecar-watcher` on Linux, run `make submodules` so CERT-V1 schema is present.

## What this is not

- Not PCS `EvidenceBundle.v0` verification — see [PCS quickstart](../pcs/quickstart.md)
- Not `so bundle pack` tar spec archives

## Next

- [Bundle walkthrough](evidence-bundle-walkthrough.md)
- [Roadmap](../roadmap/evidence-v0.1.md)
