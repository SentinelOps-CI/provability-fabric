# Proof-Carrying Science (PCS) in Provability Fabric

Provability Fabric verifies and signs scientific claim bundles from the [pcs-core](https://github.com/SentinelOps-CI/pcs-core) artifact vocabulary. This repo is the **release admission controller**: it checks bundle consistency, enforces admission profiles, validates release-chain artifacts, and produces signed bundles for downstream import.

## Prerequisites

Clone [pcs-core](https://github.com/SentinelOps-CI/pcs-core) as a sibling directory (or set `PCS_CORE_PATH`):

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
export PCS_CORE_PATH=../pcs-core
```

Optional siblings for the full cross-repo demo: [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym), [CertifyEdge](https://github.com/fraware/CertifyEdge), [scientific-memory](https://github.com/fraware/scientific-memory).

## Documentation map

| Guide | What you will do |
|-------|------------------|
| [Quickstart](quickstart.md) | Verify, sign, and inspect a bundle in five minutes |
| [Verification](verification.md) | Release mode, handoff, registry, formal checks, 17 consistency rules |
| [Admission benchmarks](admission-benchmarks.md) | Run and validate release admission benchmarks |
| [Clean checkout chain](clean-checkout-chain.md) | End-to-end cross-repo release workflow |
| [Fixtures](fixtures.md) | Regenerate frozen release and conformance fixtures |
| [Glossary](glossary.md) | Terms used across PCS docs |
| [Release checklist](release-checklist.md) | Pre-tag verification steps |

## Repository layout

| Path | Role |
|------|------|
| `adapters/pcs/` | Verification engine and admission profiles |
| `core/cli/pf/` | `pf` CLI: verify, sign, inspect, validate, explain, benchmark |
| `config/schemas/pcs/` | Schema mirror synced from pcs-core |
| `tests/pcs/fixtures/` | Conformance and release evidence fixtures |
| `benchmarks/admission/` | Admission benchmark case definitions |
| `benchmark_runs/` | Generated benchmark output (not source of truth) |
| `tools/pcs-validate/` | Fixture matrix validator |
| `release-run/` | Atomic working directory for a full release run |

The `_ci_sim_pcs/` directory is a local mirror used for isolated checks. Do not treat it as canonical; use a real `pcs-core` checkout for schema validation and `pcs validate`.

## Local quality gates

Run the same gates as [PCS CI](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/pcs-ci.yml):

```bash
make test-pcs-full
```

Individual targets:

```bash
make test-pcs                  # Go unit tests (adapter + pf CLI)
make test-pcs-rc-gate        # Release fixture identity lock
make test-pcs-phase2         # Release protocol artifact tests
make validate-pcs-fixtures   # Schema matrix on tests/pcs
make test-pcs-benchmark      # All admission benchmark suites
make pcs-bench-producer      # LabTrust ingest producer gate
make demo-pcs                # Quick verify / sign / inspect
```

## Admission profiles

Built-in profiles live under `adapters/pcs/admission_profiles/`:

| Profile ID | Workflow |
|------------|----------|
| `labtrust_qc_release` | Hospital lab QC release (`ScienceClaimBundle` + trace certificate) |
| `agent_tool_use_safety` | Agent tool-use safety |
| `scientific_computation_reproducibility` | Reproducible scientific computation |
| `formal_trust_kernel` | Formal proof obligations and Lean check results (used with labtrust release) |

## Related repos

- **pcs-core** — canonical schemas, Python `pcs validate`, example fixtures
- **LabTrust-Gym** — simulates lab runs and exports bundles
- **CertifyEdge** — temporal certificates
- **Scientific Memory** — imports signed bundles

Developer package index: [adapters/pcs/README.md](../../adapters/pcs/README.md).
