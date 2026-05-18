// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// FailureCodeLegacyHandoffForbiddenInReleaseMode is emitted when pf_handoff.json is used with --release-mode.
const FailureCodeLegacyHandoffForbiddenInReleaseMode = "legacy_handoff_forbidden_in_release_mode"

// LegacyHandoffWarning is printed when legacy pf_handoff.json is used outside release mode.
const LegacyHandoffWarning = "warning: legacy pf_handoff.json is accepted for local development only; use HandoffManifest.v0 for --release-mode"

// ReleaseAdmissionPolicy configures mandatory Phase 2 inputs in release mode.
type ReleaseAdmissionPolicy struct {
	ReleaseMode                   bool
	AllowMissingHandoff           bool
	AllowSkippedRegistrySemantics bool
}

// IsLegacy reports whether the handoff was loaded from legacy pf_handoff.json.
func (h *LoadedHandoff) IsLegacy() bool {
	return h != nil && h.Legacy != nil
}

// EnforceScienceClaimAdmission returns an error when release-mode requirements are not met.
func EnforceScienceClaimAdmission(policy ReleaseAdmissionPolicy, handoff *LoadedHandoff, registry *ArtifactRegistry, profile *AdmissionProfile) error {
	_ = profile
	if !policy.ReleaseMode {
		return nil
	}
	if !policy.AllowMissingHandoff && handoff == nil {
		return fmt.Errorf("%s: release-mode requires --handoff HandoffManifest.v0 (or --allow-missing-handoff-for-local-dev)",
			FailureCodeReleaseModeHandoffRequired)
	}
	if handoff != nil {
		if handoff.Legacy != nil {
			return fmt.Errorf("%s: legacy pf_handoff.json is forbidden in release mode; pass HandoffManifest.v0 via --handoff",
				FailureCodeLegacyHandoffForbiddenInReleaseMode)
		}
		if handoff.Manifest == nil {
			return fmt.Errorf("%s: release-mode requires HandoffManifest.v0 via --handoff", FailureCodeReleaseModeHandoffRequired)
		}
	}
	if registry == nil {
		return fmt.Errorf("%s: release-mode requires --registry ArtifactRegistry.v0 (or set PCS_CORE_PATH for default artifact_registry.valid.json)",
			FailureCodeReleaseModeRegistryRequired)
	}
	return nil
}

// EnforceReleaseChainAdmission returns an error when release-chain release-mode requirements are not met.
func EnforceReleaseChainAdmission(policy ReleaseAdmissionPolicy, manifestPath string, registry *ArtifactRegistry) error {
	if !policy.ReleaseMode {
		return nil
	}
	if strings.TrimSpace(manifestPath) == "" {
		return fmt.Errorf("%s: release-mode requires --manifest ReleaseManifest.v0", FailureCodeReleaseModeManifestRequired)
	}
	if registry == nil {
		return fmt.Errorf("%s: release-mode requires --registry ArtifactRegistry.v0 (or set PCS_CORE_PATH for default artifact_registry.valid.json)",
			FailureCodeReleaseModeRegistryRequired)
	}
	return nil
}
