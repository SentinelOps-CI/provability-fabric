# PCS release-run (atomic handoff)

Single working directory for a full PCS v0.1 release candidate. Do not copy PF outputs into fixtures repo-by-repo.

## Layout

Populated by upstream repos (LabTrust, CertifyEdge, Scientific Memory) and PF:

- `science_claim_bundle.certified.json` — from LabTrust-Gym `examples/pcs_qc_release/release/`
- `verification_result.json` — `pf verify --release-mode`
- `signed_science_claim_bundle.json` — `pf sign --release-mode` (same certified input)
- `RELEASE_FIXTURE_MANIFEST.json` — cross-repo commit and content hashes

## PF-only refresh

```bash
make freeze-pcs-labtrust-release
```

This runs `pcs-release-run-pf.sh` then `pcs-release-run-promote.sh`, which validates certificate ID alignment before copying to `tests/pcs/fixtures/labtrust-release/` and `pcs-core/examples/labtrust-release/`.

Documentation: [docs/pcs/fixtures.md](../docs/pcs/fixtures.md).
