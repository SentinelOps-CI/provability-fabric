# Proof-Carrying Science (PCS) in Provability Fabric

Provability Fabric verifies and signs scientific claim bundles that follow the [pcs-core](https://github.com/SentinelOps-CI/pcs-core) artifact vocabulary. In this repository, the release admission controller checks bundle consistency, enforces admission profiles, validates release-chain artifacts, and produces signed bundles that downstream systems can import.

## Prerequisites

Clone [pcs-core](https://github.com/SentinelOps-CI/pcs-core) as a sibling directory, or point `PCS_CORE_PATH` at an existing checkout.

```bash
git clone https://github.com/SentinelOps-CI/pcs-core ../pcs-core
export PCS_CORE_PATH=../pcs-core
```

For the full cross-repo demonstration, you may also clone [LabTrust-Gym](https://github.com/fraware/LabTrust-Gym), [CertifyEdge](https://github.com/fraware/CertifyEdge), and [scientific-memory](https://github.com/fraware/scientific-memory) beside this repository.

## Documentation map

| Guide | What you will do |
|-------|------------------|
| [Quickstart](quickstart.md) | Verify, sign, and inspect a bundle in five minutes |
| [Verification](verification.md) | Release mode, handoff, registry, formal checks, 17 consistency rules |
| [Admission benchmarks](admission-benchmarks.md) | Run and validate release admission benchmarks |
| [Clean checkout chain](clean-checkout-chain.md) | End-to-end cross-repo release workflow |
| [Fixtures](fixtures.md) | Regenerate frozen release and conformance fixtures |
| [Glossary](glossary.md) | Terms used across PCS documentation |
| [Release checklist](release-checklist.md) | Pre-tag verification steps |

## Repository layout

| Path | Role |
|------|------|
| `adapters/pcs/` | Verification engine and admission profiles |
| `core/cli/pf/` | `pf` CLI for verify, sign, inspect, validate, explain, and benchmark |
| `config/schemas/pcs/` | Schema mirror synced from pcs-core |
| `tests/pcs/fixtures/` | Conformance and release evidence fixtures |
| `benchmarks/admission/` | Admission benchmark case definitions |
| `benchmark_runs/` | Ephemeral benchmark output; committed fixtures under `tests/pcs/` remain authoritative |
| `tools/pcs-validate/` | Fixture matrix validator |
| `release-run/` | Atomic working directory for a full release run |

The `_ci_sim_pcs/` directory holds a local mirror for isolated checks. Treat a real `pcs-core` checkout as the canonical source for schema validation and for the `pcs validate` command.

## Local quality gates

Run the same gates as [PCS CI](https://github.com/SentinelOps-CI/provability-fabric/blob/main/.github/workflows/pcs-ci.yml).

```bash
make test-pcs-full
```

Individual targets include the following.

```bash
make test-pcs                 # Unit tests (adapter + pf CLI)
make test-pcs-rc-gate         # Release fixture identity lock
make test-pcs-phase2          # Handoff, registry, and release-chain tests
make validate-pcs-fixtures    # Schema matrix on tests/pcs
make test-pcs-benchmark       # All admission benchmark suites
make pcs-bench-producer       # LabTrust ingest producer gate
make demo-pcs                 # Quick verify / sign / inspect
make pcs-release-gate         # Sync schemas + full gate + demos + clean chain
```

## Admission profiles

Built-in profiles live under `adapters/pcs/admission_profiles/`.

| Profile ID | Workflow |
|------------|----------|
| `labtrust_qc_release` | Hospital lab QC release (`ScienceClaimBundle` + trace certificate) |
| `agent_tool_use_safety` | Agent tool-use safety |
| `scientific_computation_reproducibility` | Reproducible scientific computation |
| `formal_trust_kernel` | Formal proof obligations and Lean check results (used with labtrust release) |

## Related repos

| Repository | Role |
|------------|------|
| **pcs-core** | Canonical schemas, Python `pcs validate`, and example fixtures |
| **LabTrust-Gym** | Simulates lab runs and exports bundles |
| **CertifyEdge** | Temporal certificates |
| **Scientific Memory** | Imports signed bundles |

The developer package index is in [adapters/pcs/README.md](https://github.com/SentinelOps-CI/provability-fabric/blob/main/adapters/pcs/README.md).
