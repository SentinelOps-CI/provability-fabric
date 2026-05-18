# Provability Fabric — pcs-pf-v0.1.0-rc2

Release candidate **rc2** makes Provability Fabric the **profile-aware admission controller** for all PCS workflows. PF admits or rejects releases using `HandoffManifest.v0`, `ArtifactRegistry.v0`, and an explicit **admission profile** in release mode.

## Changes from rc1

- **Admission profiles** (`adapters/pcs/admission_profiles/`): `schema.json`, `labtrust_qc_release`, `agent_tool_use_safety`.
- **Release mode** requires `--admission-profile` (or `PF_ADMISSION_PROFILE`); failures: `missing_admission_profile`, `unknown_admission_profile`, `admission_profile_workflow_mismatch`, `admission_profile_required_artifact_missing`.
- **Registry semantic audit**: every registry check records `executed_passed`, `executed_failed`, `deferred_with_reason`, or `skipped_non_release` in `ReleaseChainValidationResult.v0`.
- **`pf explain`**: `pf explain release-chain <rcvr.json>` and `pf explain failure <vr.json>` with failure code, component, artifact path, expected/actual, registry/handoff refs, repair command (`--json` supported).
- **Tool-use skeleton**: `agent_tool_use_safety` validates `ScienceClaimBundle.v0` with `ToolUseTrace.v0` / `ToolUseCertificate.v0` and rejects incomplete bundles with precise failure codes (full verify path returns `tool_use_release_not_implemented` until workflow artifacts ship).
- Legacy `pf_handoff.json` is forbidden in `--release-mode`.

## Verify and sign (LabTrust QC release)

```bash
export PF_SOURCE_COMMIT="$(git rev-parse HEAD)"
export PF_RELEASE_MODE=1 PF_DETERMINISTIC=1

go -C core/cli/pf run . verify science-claim \
  tests/pcs/fixtures/labtrust-release/science_claim_bundle.certified.json \
  --handoff tests/pcs/fixtures/labtrust-release/handoff_to_pf.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --admission-profile adapters/pcs/admission_profiles/labtrust_qc_release.json \
  --release-mode \
  --out /tmp/verification_result.json

go -C core/cli/pf run . verify release-chain \
  --manifest tests/pcs/fixtures/labtrust-release/release_manifest.json \
  --registry tests/pcs/fixtures/labtrust-release/artifact_registry.json \
  --artifact-dir tests/pcs/fixtures/labtrust-release \
  --admission-profile labtrust_qc_release \
  --release-mode \
  --out /tmp/release_chain_validation_result.json

go -C core/cli/pf run . explain failure /tmp/verification_result.json
go -C core/cli/pf run . explain release-chain /tmp/release_chain_validation_result.json --json
```

## Admission profiles

| Profile | Workflow | Bundle |
|---------|----------|--------|
| `labtrust_qc_release` | `labtrust.qc_release_v0` | `ScienceClaimBundle.v0` + `TraceCertificate.v0` |
| `agent_tool_use_safety` | `agent_tool_use.safety_v0` | `ScienceClaimBundle.v0` + tool-use artifacts (skeleton) |

## Tag

Git tag: `pcs-pf-v0.1.0-rc2` on the commit that includes profile-aware admission, auditable registry checks, and PCS CI coverage.

See [pcs-pf-v0.1.0-rc1.md](./pcs-pf-v0.1.0-rc1.md) for verification semantics and RC identity pins.
