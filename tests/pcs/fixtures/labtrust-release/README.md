# LabTrust + CertifyEdge release fixtures

Real release candidate from LabTrust-Gym `examples/pcs_qc_release/release/`, plus PF-generated verification and signed wrappers.

| File | Source |
|------|--------|
| `science_claim_bundle.certified.json` | `LabTrust-Gym/examples/pcs_qc_release/release/science_claim_bundle.certified.json` |
| `verification_result.json` | `pf verify science-claim ... --out` |
| `signed_science_claim_bundle.json` | `pf sign science-claim ... --out` |

Negative fixtures (`invalid_*.json`) are derived from the certified bundle by `scripts/pcs-freeze-labtrust-release-invalid.py`.

Regenerate everything:

```bash
make freeze-pcs-labtrust-release
```

Requires LabTrust-Gym cloned beside provability-fabric (or `LABTRUST_GYM_ROOT`).
