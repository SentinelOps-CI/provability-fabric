# Evidence v0.1 quickstart

Get from clone to validated bundle in a few commands.

## Prerequisites

- Go 1.23+
- Python 3.10+ with `jsonschema` and `pytest` for tests
- Repository root as working directory

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

## What this is not

- Not PCS `EvidenceBundle.v0` verification — see [PCS quickstart](../pcs/quickstart.md)
- Not `so bundle pack` tar spec archives

## Next

- [Bundle walkthrough](evidence-bundle-walkthrough.md)
- [Roadmap](../roadmap/evidence-v0.1.md)
