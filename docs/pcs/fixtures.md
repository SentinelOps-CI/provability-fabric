# PCS fixtures

Frozen fixtures under `tests/pcs/` support CI, local gates, and release evidence. Update release evidence through a single atomic chain run instead of editing files one at a time.

## Fixture directories

| Directory | Purpose |
|-----------|---------|
| `tests/pcs/fixtures/labtrust/` | Conformance reference for schema validation |
| `tests/pcs/fixtures/labtrust-release/` | Frozen LabTrust QC release chain (release evidence) |
| `tests/pcs/fixtures/computation-release/` | Scientific computation reproducibility release train |
| `tests/pcs/fixtures/computation/` | Computation admission profile positive and negative cases |
| `tests/pcs/fixtures/tool-use/` | Tool-use admission profile cases |
| `release-run/` | Working directory for an in-progress full release run |

Negative examples for invalid cases appear under `tests/pcs/fixtures/labtrust-release-invalid/` and in pcs-core `examples/computation-release-invalid/`.

## LabTrust release fixtures

`tests/pcs/fixtures/labtrust-release/` contains the certified bundle, handoff, registry, release manifest, verification result, signed bundle, and release-chain validation result from one atomic cross-repo run.

### Regenerate (full chain)

1. Run the clean-checkout chain from LabTrust-Gym (see [Clean checkout chain](clean-checkout-chain.md)).

2. Freeze into this repository.

   ```bash
   make freeze-pcs-labtrust-release
   ```

   The freeze step requires LabTrust-Gym beside this repo. It sets `PF_SOURCE_COMMIT` from `git rev-parse HEAD`, enables release mode, and rejects placeholder commits on PF outputs.

### Sync from pcs-core

When pcs-core examples update without a full chain run, sync fixtures with the following commands.

```bash
export PCS_CORE_PATH=../pcs-core
make sync-pcs-rc-fixtures
```

### PF-only refresh of signed fixture

```bash
make freeze-pcs-labtrust-signed
```

### Release-run workflow

Use `release-run/` as the atomic handoff directory, then promote with `make freeze-pcs-labtrust-release`. See [release-run/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/release-run/README.md).

### Validate

```bash
make validate-pcs-fixtures
cd tools/pcs-validate && go run . --fixtures ../../tests/pcs

# pcs-core (requires pip install -e ../pcs-core/python)
pcs validate tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json
```

## Computation release fixtures

`tests/pcs/fixtures/computation-release/` is the reproducibility workflow release train.

Regenerate from pcs-core with the following commands.

```bash
export PCS_CORE_PATH=../pcs-core
make sync-pcs-computation-fixtures
python3 scripts/refresh-release-manifest-pins.py tests/pcs/fixtures/computation-release
```

Artifacts include dataset, environment, and computation receipts, a computation witness, a certified bundle, a signed bundle, a release manifest, and a release-chain validation result.

## Schema sync

Keep PF schemas aligned with pcs-core.

```bash
make validate-pcs-schema-diff   # compare only
make sync-pcs-schemas           # copy from pcs-core
```

## Manifest pins

After syncing release fixtures, refresh manifest pins.

```bash
python3 scripts/refresh-release-manifest-pins.py tests/pcs/fixtures/labtrust-release
python3 scripts/refresh-release-manifest-pins.py tests/pcs/fixtures/computation-release
```

`FIXTURE_MANIFEST.json` (or `RELEASE_FIXTURE_MANIFEST.json`) records repository commits and file digests for the atomic run.
