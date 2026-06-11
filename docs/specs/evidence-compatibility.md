# Evidence compatibility matrix

Evidence v0.1 is a distinct JSON bundle lane. This matrix maps existing platform surfaces without conflating domains.

## Runtime CERT-V1

| Platform artifact | v0.1 mapping | Notes |
|-------------------|--------------|-------|
| `evidence/certs/<session>/<seq>.cert.json` | Attestation-compatible ref (`application/vnd.cert-v1+json`) | External CERT-V1 schema |
| `evidence/logs/sidecar.jsonl` | Source for binding events | Additive `evidence_v01_binding` lines |

## TRACE-REPLAY-KIT

| Platform artifact | v0.1 mapping | Notes |
|-------------------|--------------|-------|
| Trace JSON / replay bundle | `execution-trace` role artifact | Referenced by digest; replay CLI checks trace self-digest |
| `so trace run` | Unchanged | v0.1 replay wraps bundle checks only |

## SWE-bench runs

| Run artifact | v0.1 mapping | Notes |
|--------------|--------------|-------|
| `metadata.json` | Optional bundle metadata sidecar | Document-only in v0.1 |
| `predictions.pfmeta.jsonl` | Cross-links hashes | Related, not identical to v0.1 bundle |
| `replay_bundle.json` | May inform execution-trace refs | Compatibility documented; no automatic conversion in v0.1 |

## PCS EvidenceBundle.v0

| PCS artifact | Relationship | Gap |
|--------------|--------------|-----|
| Science claim bundles | Related domain | Different schema, admission, and CLI (`pcs` adapters) |
| Signed science claim bundles | Not interchangeable | Use PCS verification docs |

## Spec bundles (`so bundle pack`)

| Artifact | Relationship |
|----------|--------------|
| tar.gz spec archives | Out of scope — not Evidence v0.1 JSON bundles |

## Platform gaps (honest)

| Gap | Mitigation in v0.1 |
|-----|-------------------|
| Windows bash testbed | CI runs on `ubuntu-latest`; local Windows may skip bash scripts |
| Missing `external/CERT-V1` clone | cert validator fails closed; CI clones where configured |
| Shallow `check-trace` | Documented in roadmap; not claimed as trace validator |
