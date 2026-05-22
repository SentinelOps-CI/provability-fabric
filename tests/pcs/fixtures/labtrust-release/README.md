# LabTrust release fixtures

Frozen **release evidence** for the hospital lab QC release workflow. Files come from one atomic cross-repo chain run and must not be edited individually.

Conformance-only fixtures (not release evidence): [`../labtrust/`](../labtrust/).

## Regenerate

From provability-fabric root:

```bash
make freeze-pcs-labtrust-release
```

Requires LabTrust-Gym as a sibling repo. See [PCS fixtures](../../../../docs/pcs/fixtures.md) and [Clean checkout chain](../../../../docs/pcs/clean-checkout-chain.md).

Sync examples from pcs-core without a full chain:

```bash
export PCS_CORE_PATH=../pcs-core
make sync-pcs-rc-fixtures
```

## Validate

```bash
make validate-pcs-fixtures
make test-pcs-rc-gate
```

With pcs-core installed:

```bash
pcs validate tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json
```

Invalid negative example: [`../labtrust-release-invalid/mixed_certificate_id/`](../labtrust-release-invalid/mixed_certificate_id/).
