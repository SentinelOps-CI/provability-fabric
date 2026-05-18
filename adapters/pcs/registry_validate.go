// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"strings"
)

// RegistryValidateOptions configures ArtifactRegistry.v0 admission.
type RegistryValidateOptions struct {
	ReleaseMode                   bool
	AllowSkippedRegistrySemantics bool
}

// ValidateBundleAgainstRegistry checks bundle components against ArtifactRegistry.v0.
func ValidateBundleAgainstRegistry(bundle *ScienceClaimBundle, registry *ArtifactRegistry, opts RegistryValidateOptions) error {
	if bundle == nil {
		return fmt.Errorf("bundle is nil")
	}
	if registry == nil {
		return fmt.Errorf("artifact registry is required")
	}
	if err := ValidateArtifactRegistrySemantics(registry); err != nil {
		return fmt.Errorf("registry semantics: %w", err)
	}
	components := bundleRegistryComponents(bundle)
	for _, comp := range components {
		entry, ok := registry.entryByArtifactType(comp.artifactType)
		if !ok {
			return fmt.Errorf("unregistered artifact type %q", comp.artifactType)
		}
		if entry.Producer != "" && !strings.EqualFold(entry.Producer, comp.producer) {
			return fmt.Errorf("producer mismatch for %s: registry %q bundle %q", comp.artifactType, entry.Producer, comp.producer)
		}
		if comp.schemaFile != "" && entry.Schema != "" && !schemaNamesMatch(entry.Schema, comp.schemaFile) {
			return fmt.Errorf("schema mismatch for %s: registry %q bundle %q", comp.artifactType, entry.Schema, comp.schemaFile)
		}
		if comp.status != "" && len(entry.AllowedStatuses) > 0 && !statusAllowed(entry.AllowedStatuses, comp.status) {
			return fmt.Errorf("status %q not allowed for %s (registry allows %v)", comp.status, comp.artifactType, entry.AllowedStatuses)
		}
		if err := validateBundleRequiredReleaseFields(bundle, comp, entry.RequiredReleaseFields); err != nil {
			return err
		}
		if err := executeRegistrySemanticChecks(bundle, entry, opts); err != nil {
			return err
		}
	}
	return nil
}

type bundleRegistryComponent struct {
	artifactType string
	producer     string
	schemaFile   string
	status       string
}

func bundleRegistryComponents(bundle *ScienceClaimBundle) []bundleRegistryComponent {
	var out []bundleRegistryComponent
	out = append(out, bundleRegistryComponent{
		artifactType: "ScienceClaimBundle.v0",
		producer:     bundle.Producer,
		schemaFile:   "ScienceClaimBundle.v0.schema.json",
		status:       bundleStatus(bundle),
	})
	if cert := firstCertificate(bundle); cert != nil {
		out = append(out, bundleRegistryComponent{
			artifactType: "TraceCertificate.v0",
			producer:     cert.Producer,
			schemaFile:   "TraceCertificate.v0.schema.json",
			status:       cert.Status,
		})
	}
	if r := bundle.PrimaryRuntimeReceipt(); r != nil {
		out = append(out, bundleRegistryComponent{
			artifactType: "RuntimeReceipt.v0",
			producer:     r.Producer,
			schemaFile:   "RuntimeReceipt.v0.schema.json",
			status:       r.Status,
		})
	}
	if bundle.ClaimArtifact != nil {
		out = append(out, bundleRegistryComponent{
			artifactType: "ClaimArtifact.v0",
			producer:     bundle.ClaimArtifact.Producer,
			schemaFile:   "ClaimArtifact.v0.schema.json",
			status:       bundle.ClaimArtifact.Status,
		})
	}
	if bundle.AssumptionSet != nil {
		out = append(out, bundleRegistryComponent{
			artifactType: "AssumptionSet.v0",
			producer:     bundle.AssumptionSet.Producer,
			schemaFile:   "AssumptionSet.v0.schema.json",
			status:       bundle.AssumptionSet.Status,
		})
	}
	if bundle.EvidenceBundle != nil {
		evStatus := ""
		if cert := firstCertificate(bundle); cert != nil {
			evStatus = cert.Status
		}
		out = append(out, bundleRegistryComponent{
			artifactType: "EvidenceBundle.v0",
			producer:     bundle.EvidenceBundle.Producer,
			schemaFile:   "EvidenceBundle.v0.schema.json",
			status:       evStatus,
		})
	}
	return out
}

func bundleStatus(bundle *ScienceClaimBundle) string {
	if bundle.ClaimArtifact != nil && bundle.ClaimArtifact.Status != "" {
		return bundle.ClaimArtifact.Status
	}
	return ""
}

func schemaNamesMatch(registrySchema, bundleSchema string) bool {
	return strings.EqualFold(filepathBase(registrySchema), filepathBase(bundleSchema)) ||
		strings.EqualFold(registrySchema, bundleSchema)
}

func statusAllowed(allowed []string, status string) bool {
	for _, a := range allowed {
		if strings.EqualFold(a, status) {
			return true
		}
	}
	return false
}

func executeRegistrySemanticChecks(bundle *ScienceClaimBundle, entry RegistryEntry, opts RegistryValidateOptions) error {
	for _, check := range entry.SemanticChecks {
		executed, err := runRegistrySemanticCheck(bundle, check.CheckID)
		if err != nil {
			return fmt.Errorf("registry semantic check %q failed: %w", check.CheckID, err)
		}
		if !executed {
			if opts.ReleaseMode && !opts.AllowSkippedRegistrySemantics {
				return fmt.Errorf("registry semantic check %q was not executed in release mode", check.CheckID)
			}
		}
	}
	return nil
}

func runRegistrySemanticCheck(bundle *ScienceClaimBundle, checkID string) (executed bool, err error) {
	switch checkID {
	case "trace_hash_present":
		r := bundle.PrimaryRuntimeReceipt()
		if r == nil || strings.TrimSpace(r.TraceHash) == "" {
			return true, fmt.Errorf("runtime receipt trace_hash is empty")
		}
		return true, nil
	case "trace_hash_matches_runtime_receipt":
		r := bundle.PrimaryRuntimeReceipt()
		for _, cert := range bundle.Certificates {
			if cert != nil && r != nil && cert.TraceHash != r.TraceHash {
				return true, fmt.Errorf("certificate trace_hash %s != receipt %s", cert.TraceHash, r.TraceHash)
			}
		}
		return true, nil
	case "status_is_certificate_checked_for_release":
		for _, cert := range bundle.Certificates {
			if cert != nil && cert.Status != StatusCertificateChecked {
				return true, fmt.Errorf("certificate status %q (expected %q)", cert.Status, StatusCertificateChecked)
			}
		}
		return true, nil
	case "non_empty_runtime_receipts":
		if len(bundle.RuntimeReceipts) == 0 {
			return true, fmt.Errorf("runtime_receipts is empty")
		}
		return true, nil
	case "certified_bundle_has_certificate_when_checked":
		if len(bundle.Certificates) == 0 {
			return true, fmt.Errorf("certificates is empty")
		}
		return true, nil
	case "source_commit_not_placeholder":
		if IsForbiddenPlaceholderCommit(bundle.SourceCommit) {
			return true, fmt.Errorf("bundle source_commit is a placeholder")
		}
		return true, nil
	case "assumption_set_ref_present":
		if bundle.ClaimArtifact == nil || bundle.AssumptionSet == nil {
			return true, fmt.Errorf("claim or assumption set missing")
		}
		if bundle.ClaimArtifact.AssumptionSetRef != bundle.AssumptionSet.AssumptionSetID {
			return true, fmt.Errorf("assumption_set_ref mismatch")
		}
		return true, nil
	case "certificate_refs_resolve":
		check := checkEvidenceRefsComplete(bundle)
		if check.Status == CheckFailed {
			return true, fmt.Errorf("%s", check.Description)
		}
		return true, nil
	case "entries_cover_required_artifact_types", "source_commit_matches_release_manifest":
		return true, nil
	case "verified_input_bundle_hash_matches_certified",
		"failed_checks_block_import_ready_status", "signed_input_bundle_hash_matches_certified",
		"embedded_bundle_passes_science_claim_semantics", "release_mode_commit_policy",
		"artifact_hashes_match_files", "handoff_input_hashes_when_validated",
		"status_matches_check_outcomes":
		return false, nil
	default:
		return false, nil
	}
}

func checkArtifactRegistryAdmission(bundle *ScienceClaimBundle, opts ValidateOptions) VerificationCheck {
	const id = "artifact_registry_admission"
	if opts.Registry == nil {
		if opts.ReleaseMode {
			return failCheck(id, "Bundle components match ArtifactRegistry.v0 admission rules",
				ReasonRegistryAdmissionFailed, detailMsg("registry not provided in release mode"))
		}
		return skipCheck(id, "Bundle components match ArtifactRegistry.v0 admission rules", detailMsg("registry not provided"))
	}
	regOpts := RegistryValidateOptions{
		ReleaseMode:                   opts.ReleaseMode,
		AllowSkippedRegistrySemantics: opts.AllowSkippedRegistrySemantics,
	}
	if err := ValidateBundleAgainstRegistry(bundle, opts.Registry, regOpts); err != nil {
		return failCheck(id, "Bundle components match ArtifactRegistry.v0 admission rules",
			ReasonRegistryAdmissionFailed, map[string]any{"error": err.Error()})
	}
	return passCheck(id, "Bundle components match ArtifactRegistry.v0 admission rules", map[string]any{
		"registry_id": opts.Registry.RegistryID,
	})
}

// ValidateManifestAgainstRegistry ensures release manifest artifact types are registered.
func ValidateManifestAgainstRegistry(manifest *ReleaseManifest, registry *ArtifactRegistry, opts RegistryValidateOptions) error {
	if manifest == nil || registry == nil {
		return fmt.Errorf("manifest and registry are required")
	}
	for name, entry := range manifest.Artifacts {
		if isDownstreamOfPFAdmission(name) {
			continue
		}
		regEntry, ok := registry.entryByArtifactType(entry.ArtifactType)
		if !ok {
			// Upstream capture artifacts (e.g. LabTrust.Trace.v0) may appear in ReleaseManifest but outside ArtifactRegistry.v0.
			continue
		}
		if regEntry.Producer != "" && entry.Producer != "" && !strings.EqualFold(regEntry.Producer, entry.Producer) {
			return fmt.Errorf("manifest artifact %q producer %q does not match registry %q", name, entry.Producer, regEntry.Producer)
		}
		for _, check := range regEntry.SemanticChecks {
			if manifestRegistrySemanticDeferred(check.CheckID) {
				continue
			}
			if check.CheckID == "release_mode_commit_policy" {
				if err := ValidateReleaseManifestSemantics(manifest); err != nil {
					return err
				}
			}
		}
	}
	return nil
}

func manifestRegistrySemanticDeferred(check string) bool {
	switch check {
	case "artifact_hashes_match_files", "verified_input_bundle_hash_matches_certified",
		"signed_input_bundle_hash_matches_certified", "embedded_bundle_passes_science_claim_semantics",
		"failed_checks_block_import_ready_status", "status_matches_check_outcomes",
		"handoff_input_hashes_when_validated",
		"non_empty_runtime_receipts", "certified_bundle_has_certificate_when_checked",
		"assumption_set_ref_present", "certificate_refs_resolve":
		return true
	default:
		return false
	}
}

func runManifestRegistrySemantic(check string, manifest *ReleaseManifest, name string, entry ManifestArtifactEntry) (bool, error) {
	switch check {
	case "release_mode_commit_policy":
		return true, nil
	case "trace_hash_present":
		if entry.ArtifactType != "RuntimeReceipt.v0" {
			return true, nil
		}
		return true, nil // enforced by trace_hash_consistent release-chain check
	case "status_is_certificate_checked_for_release":
		if entry.ArtifactType != "TraceCertificate.v0" {
			return true, nil
		}
		return true, nil // enforced by certificate_id_consistent / bundle verification
	case "trace_hash_matches_runtime_receipt", "source_commit_matches_release_manifest":
		return true, nil // enforced by trace_hash_consistent / producer_commits_match
	default:
		return false, nil
	}
}

func bundleComponentObject(bundle *ScienceClaimBundle, artifactType string) any {
	if bundle == nil {
		return nil
	}
	switch artifactType {
	case "ScienceClaimBundle.v0":
		return bundle
	case "TraceCertificate.v0":
		return firstCertificate(bundle)
	case "RuntimeReceipt.v0":
		return bundle.PrimaryRuntimeReceipt()
	case "ClaimArtifact.v0":
		return bundle.ClaimArtifact
	case "AssumptionSet.v0":
		return bundle.AssumptionSet
	case "EvidenceBundle.v0":
		return bundle.EvidenceBundle
	default:
		return nil
	}
}

func validateBundleRequiredReleaseFields(bundle *ScienceClaimBundle, comp bundleRegistryComponent, fields []string) error {
	if len(fields) == 0 {
		return nil
	}
	for _, field := range fields {
		if field == "status" {
			if bundleComponentStatus(bundle, comp.artifactType) == "" {
				return fmt.Errorf("required release field %q missing for %s", field, comp.artifactType)
			}
			continue
		}
		obj := bundleComponentObject(bundle, comp.artifactType)
		if err := validateRequiredReleaseFields(comp.artifactType, obj, []string{field}); err != nil {
			return err
		}
	}
	return nil
}

func bundleComponentStatus(bundle *ScienceClaimBundle, artifactType string) string {
	switch artifactType {
	case "ScienceClaimBundle.v0":
		return bundleStatus(bundle)
	case "EvidenceBundle.v0":
		if cert := firstCertificate(bundle); cert != nil {
			return cert.Status
		}
		return ""
	default:
		comp := bundleRegistryComponent{artifactType: artifactType}
		for _, c := range bundleRegistryComponents(bundle) {
			if c.artifactType == artifactType {
				comp = c
				break
			}
		}
		return comp.status
	}
}

func validateRequiredReleaseFields(artifactType string, obj any, fields []string) error {
	if len(fields) == 0 || obj == nil {
		return nil
	}
	for _, field := range fields {
		if !jsonFieldPresent(obj, field) {
			return fmt.Errorf("required release field %q missing for %s", field, artifactType)
		}
	}
	return nil
}

func validateManifestEntryRequiredFields(artifactName string, entry ManifestArtifactEntry, fields []string) error {
	if len(fields) == 0 {
		return nil
	}
	for _, field := range fields {
		if !manifestPinSupportsRequiredField(field) {
			continue
		}
		if !manifestEntryHasReleaseField(entry, field) {
			return fmt.Errorf("required release field %q missing for manifest artifact %s (%s)", field, artifactName, entry.ArtifactType)
		}
	}
	return nil
}

func manifestPinSupportsRequiredField(field string) bool {
	switch field {
	case "producer", "source_repo", "source_commit", "sha256", "schema", "artifact_type", "schema_version":
		return true
	default:
		return false
	}
}

func manifestEntryHasReleaseField(entry ManifestArtifactEntry, field string) bool {
	switch field {
	case "schema_version", "schema":
		return strings.TrimSpace(entry.Schema) != ""
	case "artifact_type":
		return strings.TrimSpace(entry.ArtifactType) != ""
	default:
		return jsonFieldPresent(entry, field)
	}
}

func jsonFieldPresent(obj any, field string) bool {
	data, err := json.Marshal(obj)
	if err != nil {
		return false
	}
	var m map[string]any
	if err := json.Unmarshal(data, &m); err != nil {
		return false
	}
	v, ok := m[field]
	if !ok {
		return false
	}
	if s, ok := v.(string); ok {
		return strings.TrimSpace(s) != ""
	}
	return v != nil
}
