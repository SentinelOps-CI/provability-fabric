# PCS adapter (Provability Fabric)

Verifies and signs `ScienceClaimBundle.v0` artifacts for the Proof-Carrying Lab Workflow v0.1 demo.

## Responsibilities

- Load LabTrust-certified science claim bundles
- Run required consistency and provenance checks
- Emit `VerificationResult.v0`
- Build `SignedScienceClaimBundle.v0` wrappers for Scientific Memory import

## Usage (via CLI)

```bash
pf verify science-claim tests/pcs/valid_labtrust_bundle.json
pf sign science-claim tests/pcs/valid_labtrust_bundle.json --out /tmp/signed.json
pf inspect science-claim /tmp/signed.json
```

Canonical artifact vocabulary lives in [pcs-core](https://github.com/SentinelOps-CI/pcs-core).
