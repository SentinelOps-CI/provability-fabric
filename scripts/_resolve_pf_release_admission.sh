# shellcheck shell=bash
# Resolve HandoffManifest.v0 and ArtifactRegistry.v0 paths for PF release-mode scripts.
# Source after setting ROOT, LABTRUST (or LABTRUST_GYM_ROOT), and optional PCS_CORE.

resolve_pf_handoff() {
  local release_dir="$1"
  local pcs_core="${2:-}"
  local candidates=(
    "${release_dir}/handoff_to_pf.json"
    "${release_dir}/handoff_manifest.bundle_to_verifier.v0.json"
  )
  local f
  for f in "${candidates[@]}"; do
    if [[ -f "${f}" ]]; then
      echo "${f}"
      return 0
    fi
  done
  if [[ -n "${pcs_core}" ]]; then
    for f in \
      "${pcs_core}/examples/labtrust-release/handoff_to_pf.json" \
      "${pcs_core}/examples/labtrust-release/handoff_manifest.bundle_to_verifier.v0.json"; do
      if [[ -f "${f}" ]]; then
        echo "${f}"
        return 0
      fi
    done
  fi
  return 1
}

resolve_pf_registry() {
  local release_dir="$1"
  local pcs_core="${2:-}"
  local root="${3:-}"
  local candidates=(
    "${release_dir}/artifact_registry.json"
    "${release_dir}/artifact_registry.v0.json"
  )
  local f
  for f in "${candidates[@]}"; do
    if [[ -f "${f}" ]]; then
      echo "${f}"
      return 0
    fi
  done
  if [[ -n "${pcs_core}" && -f "${pcs_core}/examples/artifact_registry.valid.json" ]]; then
    echo "${pcs_core}/examples/artifact_registry.valid.json"
    return 0
  fi
  if [[ -n "${root}" && -f "${root}/tests/pcs/fixtures/labtrust-release/artifact_registry.json" ]]; then
    echo "${root}/tests/pcs/fixtures/labtrust-release/artifact_registry.json"
    return 0
  fi
  return 1
}
