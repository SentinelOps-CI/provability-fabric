# Provability Fabric — pcs-pf-v0.1.0-rc1

Provability Fabric (PF) is the verification and signing layer in the Proof-Carrying Science (PCS) v0.1 release candidate. PF consumes a **certified** `ScienceClaimBundle.v0` from LabTrust/CertifyEdge and emits artifacts Scientific Memory can import.

Canonical release fixtures live in [pcs-core `examples/labtrust-release/`](https://github.com/SentinelOps-CI/pcs-core/tree/main/examples/labtrust-release). PF must not drift from that directory.

## What PF verifies

PF runs seventeen structural and consistency checks on `ScienceClaimBundle.v0` (frozen RC signed bundles may still embed fifteen checks from the RC generation commit):

- pcs-core JSON Schema validity (`schema_version` v0, `runtime_receipts[]`, `certificates[]`)
- Presence of claim, assumption set, runtime receipt, trace certificate, and evidence bundle
- Trace hash alignment between receipt and certificate
- Certificate status `CertificateChecked`
- Evidence reference completeness
- Non-stale artifacts
- Source provenance (`source_repo`, `source_commit`)
- Release-mode rejection of placeholder commits

On success PF writes `VerificationResult.v0` with `status: ProofChecked`, seventeen `checks` (including status-transition policy), `verified_input` (bundle file hash, certificate ID, trace hash), and `signature_or_digest`.

Optional `--handoff` accepts legacy `pf_handoff.json` or pcs-core `HandoffManifest.v0` and ensures the bundle matches LabTrust release pins before verify/sign.

Phase 2 admission commands:

```bash
pf verify release-chain \
  --manifest release_manifest.json \
  --artifact-dir /path/to/labtrust-release \
  --out release_chain_validation_result.json

pf verify science-claim science_claim_bundle.certified.json \
  --handoff handoff_to_pf.json \
  --registry release_manifest.json \
  --release-chain-result release_chain_validation_result.json
```

`--registry` loads `ReleaseManifest.v0` (artifact registry until `ArtifactRegistry.v0` is published in pcs-core).

## What PF signs

After verification passes, PF wraps the **exact** certified bundle in `SignedScienceClaimBundle.v0`:

- Embeds the full `science_claim_bundle` and `verification_result`
- Sets `signed_input_bundle_hash` to the certified JSON file digest
- Records PF `source_commit` and wrapper `signature_or_digest`

Signing refuses failed verification, handoff mismatch, and placeholder commits in release mode.

## What PF does not prove

PF does **not**:

- Re-run LabTrust trace capture or CertifyEdge certification
- Prove correctness of scientific claims, models, or experiment outcomes
- Replace pcs-core or Scientific Memory validation
- Guarantee byte-identical bundles across tools unless the same certified file and PF commit are used

PF proves the certified bundle passed PF’s v0.1 checks at signing time and that the signed wrapper digests are internally consistent.

## Inspect the signed bundle

```bash
# From repository root
go -C core/cli/pf run . inspect science-claim \
  tests/pcs/fixtures/labtrust-release/signed_science_claim_bundle.json \
  --strict
```

`--strict` requires PF-computed digests on the embedded verification result and wrapper. `--reverify` re-runs all current PF checks on the embedded bundle.

Validate Phase 2 protocol artifacts:

```bash
go -C core/cli/pf run . validate handoff-manifest tests/pcs/fixtures/labtrust-release/handoff_to_pf.json
go -C core/cli/pf run . validate release-manifest tests/pcs/fixtures/labtrust-release/release_manifest.json
go -C core/cli/pf run . validate release-chain-result tests/pcs/fixtures/labtrust-release/release_chain_validation_result.json
```

## Reproduce the verification result

Sync fixtures from pcs-core (do not edit PF outputs by hand):

```bash
make sync-pcs-rc-fixtures
# PCS_CORE_PATH=../pcs-core python scripts/pcs-sync-from-pcs-core-rc.py
```

Regenerate PF outputs only as part of the full upstream release chain, then re-sync:

```bash
# Requires LabTrust-Gym beside this repo
make freeze-pcs-labtrust-release
```

Verify and sign the certified bundle (release mode, with LabTrust handoff):

```bash
export PF_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PF_RELEASE_MODE=1 PF_DETERMINISTIC=1

go -C core/cli/pf run . verify science-claim \
  tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff ../LabTrust-Gym/examples/pcs_qc_release/release/pf_handoff.json \
  --release-mode --out /tmp/verification_result.json

go -C core/cli/pf run . sign science-claim \
  tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff ../LabTrust-Gym/examples/pcs_qc_release/release/pf_handoff.json \
  --release-mode --out /tmp/signed_science_claim_bundle.json
```

Lock tests (require pcs-core checkout):

```bash
make test-pcs-full   # unit + RC lock + Phase 2 + fixture matrix
make test-pcs-rc-gate
```

## Canonical RC identity (PF segment)

| Field | Value |
|-------|--------|
| `verified_input.bundle_hash` / `signed_input_bundle_hash` | `sha256:9b42d792199eb6f358d26f822699f0ed65bb4366eee306d4958d42121c656833` |
| `verified_input.certificate_id` | `cert-trace-886c95f0-5d63-42d6-aa13-5891c12c5a6a` |
| `verified_input.trace_hash` | `sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd` |
| PF `source_commit` | `0f659b90c80c46a6bbfd51b0d37ea723b032fb9d` |

See pcs-core `RELEASE_FIXTURE_MANIFEST.json` for the full cross-repo commit and artifact digest chain.
