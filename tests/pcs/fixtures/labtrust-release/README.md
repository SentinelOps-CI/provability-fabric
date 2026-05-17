# LabTrust + CertifyEdge release fixtures

Canonical release candidate bundle (`scb-qc-release-rc1`) from pcs-core `examples/labtrust-release/`, with evidence refs aligned for PF verification.

| File | Source |
|------|--------|
| `science_claim_bundle.certified.json` | LabTrust pending + CertifyEdge trace certificate (pcs-core) |
| `verification_result.json` | `pf verify science-claim ... --out` |
| `signed_science_claim_bundle.json` | `pf sign science-claim ... --out` |

Regenerate:

```bash
make freeze-pcs-labtrust-release
```
