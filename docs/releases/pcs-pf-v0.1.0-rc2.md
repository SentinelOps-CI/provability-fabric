# Archived: pcs-pf-v0.1.0-rc2

Historical release candidate notes. For current documentation see [PCS documentation](../pcs/README.md).

Changes from rc1 that remain in the current release:

- Profile-aware admission (`labtrust_qc_release`, `agent_tool_use_safety`, and later `scientific_computation_reproducibility`)
- Release mode requires `--admission-profile`
- `pf explain failure` and `pf explain release-chain`
- Legacy `pf_handoff.json` forbidden in release mode

The current tree adds computation reproducibility benchmarks, four admission benchmark suites, and full tool-use profile validation. See [Admission benchmarks](../pcs/admission-benchmarks.md).
