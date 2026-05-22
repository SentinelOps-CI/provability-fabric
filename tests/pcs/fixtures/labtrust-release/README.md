# LabTrust release fixtures

Frozen **release evidence** for the hospital lab QC release workflow. Files come from one atomic cross-repo chain run and must be updated only through the freeze or sync workflows described below.

Conformance-only fixtures for schema checks live under [`../labtrust/`](../labtrust/).

## Regenerate

From the provability-fabric repository root, run the freeze target.

```bash
make freeze-pcs-labtrust-release
```

LabTrust-Gym must sit beside this repository. See [PCS fixtures](../../../../docs/pcs/fixtures.md) and [Clean checkout chain](../../../../docs/pcs/clean-checkout-chain.md).

To sync examples from pcs-core without a full chain run, use the following commands.

```bash
export PCS_CORE_PATH=../pcs-core
make sync-pcs-rc-fixtures
```

## Validate

```bash
make validate-pcs-fixtures
make test-pcs-rc-gate
```

With pcs-core installed, validate the certified bundle directly.

```bash
pcs validate tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json
```

Invalid negative example for mixed certificate IDs lives under [`../labtrust-release-invalid/mixed_certificate_id/`](../labtrust-release-invalid/mixed_certificate_id/).
