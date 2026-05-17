# PCS v0.1 clean-checkout chain

PCS v0.1 is **release-ready** only when the full cross-repo chain succeeds on a clean checkout with sibling repositories:

- [pcs-core](https://github.com/SentinelOps-CI/pcs-core)
- [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym)
- [CertifyEdge](https://github.com/fraware/CertifyEdge)
- **provability-fabric** (this repo)
- [scientific-memory](https://github.com/fraware/scientific-memory)

## One-command run

From provability-fabric (Git Bash / WSL / Linux):

```bash
export PCS_DETERMINISTIC=1
./scripts/run-pcs-v01-clean-chain.sh
```

Or:

```bash
just pcs-v01-clean-chain
```

PowerShell (delegates to LabTrust-Gym when cloned):

```powershell
$env:PCS_DETERMINISTIC = "1"
just pcs-v01-clean-chain-ps1
```

## Manual chain

Run from a **LabTrust-Gym** working directory (`examples/pcs_qc_release/` or repo root per LabTrust docs):

```bash
# LabTrust-Gym
PCS_DETERMINISTIC=1 labtrust run-demo qc-release
PCS_DETERMINISTIC=1 labtrust run-demo qc-release-invalid-missing-qc
PCS_DETERMINISTIC=1 labtrust run-demo qc-release-invalid-unauthorized

labtrust export-trace --run runs/qc-release --out trace.json
labtrust export-runtime-receipt --run runs/qc-release --out runtime_receipt.json
labtrust export-pcs --run runs/qc-release --out science_claim_bundle.pending.json
pcs validate science_claim_bundle.pending.json

# CertifyEdge
certifyedge emit-pcs-certificate \
  --spec templates/hospital_lab/qc_release.stl \
  --trace trace.json \
  --out trace_certificate.json
pcs validate trace_certificate.json
certifyedge verify-certificate trace_certificate.json --trace trace.json

# LabTrust-Gym
labtrust attach-certificate \
  --bundle science_claim_bundle.pending.json \
  --certificate trace_certificate.json \
  --out science_claim_bundle.certified.json
pcs validate science_claim_bundle.certified.json

# Provability Fabric
pf verify science-claim science_claim_bundle.certified.json \
  --out verification_result.json
pcs validate verification_result.json

pf sign science-claim science_claim_bundle.certified.json \
  --out signed_science_claim_bundle.json
pcs validate signed_science_claim_bundle.json
pf inspect science-claim signed_science_claim_bundle.json

# Scientific Memory
cd ../scientific-memory
just pcs-import-bundle ../LabTrust-Gym/signed_science_claim_bundle.json
just pcs-render-claim claim-pcs-qc-release-v0.1
```

## `pcs validate` in this repo

The `pcs` command is provided by **pcs-core** (Python). From provability-fabric root:

```bash
./pcs validate path/to/artifact.json
# or
./scripts/pcs validate path/to/artifact.json
```

Requires `../pcs-core` or `PCS_CORE_PATH`.

Provability Fabric also exposes schema validation:

```bash
pf validate verification-result verification_result.json
pf validate signed-science-claim signed_science_claim_bundle.json
```

## PF-only segment (CI / partial checkout)

When LabTrust-Gym is not cloned, run the PF segment against frozen release fixtures:

```bash
make pcs-v01-pf-chain
# or
./scripts/pcs-pf-clean-chain.sh tests/pcs/fixtures/labtrust-release
```

## Environment variables

| Variable | Default | Purpose |
|----------|---------|---------|
| `PCS_DETERMINISTIC` | `1` in chain scripts | LabTrust deterministic demos |
| `PCS_CORE_PATH` | `../pcs-core` | pcs-core checkout |
| `LABTRUST_GYM_ROOT` | `../LabTrust-Gym` | LabTrust-Gym checkout |
| `CERTIFYEDGE_ROOT` | `../CertifyEdge` | CertifyEdge checkout |
| `SCIENTIFIC_MEMORY_ROOT` | `../scientific-memory` | Scientific Memory checkout |
| `PF_SOURCE_COMMIT` | `git rev-parse HEAD` | Provenance on signed wrapper |
