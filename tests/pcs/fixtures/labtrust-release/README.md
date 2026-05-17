# LabTrust release fixtures (PCS v0.1 RC)

Canonical release candidate artifacts live in **`pcs-core/examples/labtrust-release/`**. PF fixtures here are synchronized from that directory; do not regenerate PF outputs independently unless the full release chain is promoted atomically.

| File | Source |
|------|--------|
| `science_claim_bundle.certified.json` | pcs-core RC |
| `verification_result.json` | pcs-core RC |
| `signed_science_claim_bundle.json` | pcs-core RC |
| `handoff_to_pf.json` | pcs-core `examples/labtrust-release/handoff_manifest.bundle_to_verifier.v0.json`, or `examples/handoff_manifest.valid.json` |
| `release_manifest.json` | pcs-core `examples/labtrust-release/release_manifest.v0.json`, or `examples/release_manifest.valid.json` |
| `release_chain_validation_result.json` | pcs-core `examples/labtrust-release/release_chain_validation_result.v0.json`, or `examples/release_chain_validation_result.valid.json` (reference; PF emits its own via `pf verify release-chain`) |
| `pf_handoff.json` | Derived legacy handoff (sync script) |

Negative fixtures (`invalid_*.json`) are derived from the certified bundle by `scripts/pcs-freeze-labtrust-release-invalid.py`.

Sync from pcs-core:

```bash
make sync-pcs-rc-fixtures
# or: python scripts/pcs-sync-from-pcs-core-rc.py ../pcs-core
```

Regenerate the full chain (LabTrust → CertifyEdge → PF → pcs-core) only via atomic release-run promotion upstream; then run `make sync-pcs-rc-fixtures` in this repo.
