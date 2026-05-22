# PCS glossary

Plain-language definitions for terms used in Provability Fabric PCS documentation.

| Term | Meaning |
|------|---------|
| **Proof-Carrying Science (PCS)** | Artifacts that carry verification evidence alongside scientific claims |
| **Provability Fabric (`pf`)** | CLI in this repo that verifies, signs, and inspects science claim bundles |
| **pcs-core** | Separate repository with canonical schemas, Python `pcs validate`, and example fixtures |
| **Science claim bundle** | Certified JSON document combining runtime receipts, certificates, and claim metadata |
| **Release mode** | Strict verification requiring handoff manifest, artifact registry, and an admission profile |
| **Admission profile** | Named rule set for a workflow (for example hospital QC release or tool-use safety) |
| **Handoff manifest** | Structured handoff from upstream tools to Provability Fabric (`HandoffManifest.v0`) |
| **Artifact registry** | Catalog of artifacts with allowed producers and statuses (`ArtifactRegistry.v0`) |
| **Release manifest** | Manifest listing all artifacts in a release (`ReleaseManifest.v0`) |
| **Release-chain validation result** | Report from validating an entire release against manifest and registry |
| **Proof-checked / Rejected** | Verification passed or failed |
| **Formal checks** | Machine-checked proof obligations validated from Lean outputs (PF does not run Lean) |
| **Admission benchmark** | Automated suite measuring admit/reject correctness and explain quality |
| **Benchmark ingest** | Single JSON file (`pcs_bench_ingest.v0.json`) exporting a benchmark run for downstream tools |
| **Failure localization** | Report identifying which check failed and on which artifact |
| **Conformance fixtures** | Schema-only reference bundles (`tests/pcs/fixtures/labtrust/`) |
| **Release fixtures** | Frozen evidence from a full chain run (`tests/pcs/fixtures/labtrust-release/`) |
| **Freeze / sync** | Copy outputs from a chain run into fixtures, or copy examples from pcs-core |
