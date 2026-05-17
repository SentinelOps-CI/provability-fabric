// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"fmt"
	"strings"
)

// ValidateBundleAgainstRegistry checks bundle components against ReleaseManifest.v0 artifact entries.
func ValidateBundleAgainstRegistry(bundle *ScienceClaimBundle, registry *ArtifactRegistry) error {
	if bundle == nil {
		return fmt.Errorf("bundle is nil")
	}
	if registry == nil {
		return fmt.Errorf("artifact registry is required")
	}
	if err := ValidateReleaseManifestSemantics(registry); err != nil {
		return fmt.Errorf("registry semantics: %w", err)
	}
	checks := []struct {
		artifactType string
		producer     string
		status       string
	}{
		{"ScienceClaimBundle.v0", bundle.Producer, ""},
	}
	if cert := firstCertificate(bundle); cert != nil {
		checks = append(checks, struct {
			artifactType string
			producer     string
			status       string
		}{"TraceCertificate.v0", cert.Producer, cert.Status})
	}
	if r := bundle.PrimaryRuntimeReceipt(); r != nil {
		checks = append(checks, struct {
			artifactType string
			producer     string
			status       string
		}{"RuntimeReceipt.v0", r.Producer, r.Status})
	}
	for _, art := range checks {
		entry, ok := registryEntryByType(registry, art.artifactType)
		if !ok {
			return fmt.Errorf("unregistered artifact type %q", art.artifactType)
		}
		if entry.Producer != "" && !strings.EqualFold(entry.Producer, art.producer) {
			return fmt.Errorf("producer mismatch for %s: registry %q bundle %q", art.artifactType, entry.Producer, art.producer)
		}
		if art.status != "" {
			if err := assertRegistryAllowedStatus(art.artifactType, art.status); err != nil {
				return err
			}
		}
	}
	return nil
}

func registryEntryByType(registry *ReleaseManifest, artifactType string) (ManifestArtifactEntry, bool) {
	for _, entry := range registry.Artifacts {
		if entry.ArtifactType == artifactType {
			return entry, true
		}
	}
	return ManifestArtifactEntry{}, false
}

func firstCertificate(bundle *ScienceClaimBundle) *TraceCertificate {
	for _, cert := range bundle.Certificates {
		if cert != nil {
			return cert
		}
	}
	return nil
}

func assertRegistryAllowedStatus(artifactType, status string) error {
	switch artifactType {
	case "TraceCertificate.v0":
		if status != StatusCertificateChecked {
			return fmt.Errorf("status %q not allowed for TraceCertificate.v0 (expected %q)", status, StatusCertificateChecked)
		}
	case "RuntimeReceipt.v0":
		if status == StatusStale || status == StatusRejected {
			return fmt.Errorf("status %q not allowed for RuntimeReceipt.v0", status)
		}
	}
	return nil
}

func checkArtifactRegistryAdmission(bundle *ScienceClaimBundle, opts ValidateOptions) VerificationCheck {
	const id = "artifact_registry_admission"
	if opts.Registry == nil {
		return skipCheck(id, "Bundle components match ReleaseManifest.v0 artifact registry", detailMsg("registry not provided"))
	}
	if err := ValidateBundleAgainstRegistry(bundle, opts.Registry); err != nil {
		return failCheck(id, "Bundle components match ReleaseManifest.v0 artifact registry",
			ReasonRegistryAdmissionFailed, map[string]any{"error": err.Error()})
	}
	return passCheck(id, "Bundle components match ReleaseManifest.v0 artifact registry", map[string]any{
		"release_id": opts.Registry.ReleaseID,
	})
}
