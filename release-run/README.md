# PCS release-run (atomic handoff)

Single working directory for a full PCS v0.1 release candidate. Promote outputs through the freeze scripts instead of copying PF artifacts into fixtures repository by repository.

## Layout

Upstream repositories (LabTrust, CertifyEdge, Scientific Memory) and Provability Fabric populate the directory.

- `science_claim_bundle.certified.json` comes from LabTrust-Gym `examples/pcs_qc_release/release/`
- `verification_result.json` comes from `pf verify --release-mode`
- `signed_science_claim_bundle.json` comes from `pf sign --release-mode` using the same certified input
- `RELEASE_FIXTURE_MANIFEST.json` records cross-repo commits and content hashes

## PF-only refresh

```bash
make freeze-pcs-labtrust-release
```

This runs `pcs-release-run-pf.sh` then `pcs-release-run-promote.sh`, which validates certificate ID alignment before copying to `tests/pcs/fixtures/labtrust-release/` and `pcs-core/examples/labtrust-release/`.

Documentation continues in [docs/pcs/fixtures.md](../docs/pcs/fixtures.md).
