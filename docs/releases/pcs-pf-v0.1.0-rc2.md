# Provability Fabric — pcs-pf-v0.1.0-rc2

Release candidate **rc2** aligns PF release-mode admission with pcs-core and LabTrust **HandoffManifest.v0** naming. Legacy `pf_handoff.json` remains supported only outside `--release-mode` (for local development and negative tests).

## Changes from rc1

- **Release mode** rejects legacy `pf_handoff.json` (`legacy_handoff_forbidden_in_release_mode`).
- PF `--handoff` expects `HandoffManifest.v0` (`handoff_to_pf.json` or `handoff_manifest.bundle_to_verifier.v0.json`).
- PF `--registry` is `ArtifactRegistry.v0`; `--manifest` is `ReleaseManifest.v0`.
- pcs-core `examples/labtrust-release/` ships `handoff_to_pf.json` as an alias of the bundle-to-verifier stage handoff.
- Clean-chain and release-run scripts resolve handoff/registry from LabTrust release dir, pcs-core examples, or PF fixtures.

## Verify and sign (release mode)

```bash
export PF_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PF_RELEASE_MODE=1 PF_DETERMINISTIC=1

go -C core/cli/pf run . verify science-claim \
  tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --release-mode --out /tmp/verification_result.json

go -C core/cli/pf run . sign science-claim \
  tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --release-mode --out /tmp/signed_science_claim_bundle.json
```

## Canonical handoff (pcs-core)

| PF path | pcs-core canonical |
|---------|-------------------|
| `handoff_to_pf.json` | `examples/labtrust-release/handoff_to_pf.json` (alias) |
| same payload | `handoff_manifest.bundle_to_verifier.v0.json` |

Sync PF fixtures: `make sync-pcs-rc-fixtures`

## Tag

Git tag: `pcs-pf-v0.1.0-rc2` on the commit that includes protocol-native release mode and aligned handoff manifests across pcs-core and PF.

See [pcs-pf-v0.1.0-rc1.md](./pcs-pf-v0.1.0-rc1.md) for verification semantics and RC identity pins.
