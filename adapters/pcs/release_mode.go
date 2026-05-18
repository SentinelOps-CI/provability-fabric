// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// ReleaseAdmissionPolicy configures mandatory Phase 2 inputs in release mode.
type ReleaseAdmissionPolicy struct {
	ReleaseMode                   bool
	AllowMissingHandoff           bool
	AllowSkippedRegistrySemantics bool
}

// EnforceScienceClaimAdmission returns an error when release-mode requirements are not met.
func EnforceScienceClaimAdmission(policy ReleaseAdmissionPolicy, handoff *LoadedHandoff, registry *ArtifactRegistry) error {
	if !policy.ReleaseMode {
		return nil
	}
	if !policy.AllowMissingHandoff && handoff == nil {
		return fmt.Errorf("release-mode requires --handoff (or --allow-missing-handoff-for-local-dev)")
	}
	if registry == nil {
		return fmt.Errorf("release-mode requires --registry ArtifactRegistry.v0 (or set PCS_CORE_PATH for default artifact_registry.valid.json)")
	}
	return nil
}

// EnforceReleaseChainAdmission returns an error when release-chain release-mode requirements are not met.
func EnforceReleaseChainAdmission(policy ReleaseAdmissionPolicy, manifestPath string, registry *ArtifactRegistry) error {
	if !policy.ReleaseMode {
		return nil
	}
	if strings.TrimSpace(manifestPath) == "" {
		return fmt.Errorf("release-mode requires --manifest ReleaseManifest.v0")
	}
	if registry == nil {
		return fmt.Errorf("release-mode requires --registry ArtifactRegistry.v0 (or set PCS_CORE_PATH for default artifact_registry.valid.json)")
	}
	return nil
}
