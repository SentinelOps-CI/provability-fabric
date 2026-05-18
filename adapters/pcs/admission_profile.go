// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"embed"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

//go:embed admission_profiles/*.json
var admissionProfileFS embed.FS

// StatusPolicy and RepairHintPolicy name built-in policy bundles.
type StatusPolicy string
type RepairHintPolicy string

const (
	StatusPolicyLabtrustReleaseV01  StatusPolicy = "labtrust_release_v0.1"
	StatusPolicyToolUseSafetyV01     StatusPolicy = "tool_use_safety_v0.1"
	RepairHintPolicyOperationalV0  RepairHintPolicy = "operational_v0"
)

// AdmissionProfile defines PF admission policy for a PCS workflow.
type AdmissionProfile struct {
	ProfileID                    string   `json:"profile_id"`
	Description                  string   `json:"description,omitempty"`
	AcceptedBundleArtifact       string   `json:"accepted_bundle_artifact"`
	AcceptedBundleArtifactType   string   `json:"accepted_bundle_artifact_type,omitempty"`
	RequiredRuntimeArtifacts     []string `json:"required_runtime_artifacts"`
	RequiredCertificateArtifacts []string `json:"required_certificate_artifacts"`
	RequiredCertificateArtifactTypes []string `json:"required_certificate_artifact_types,omitempty"`
	RequiredHandoffKinds         []string `json:"required_handoff_kinds"`
	RequiredHandoffKind          string   `json:"required_handoff_kind,omitempty"`
	RequiredRegistryChecks       []string `json:"required_registry_checks"`
	RegistryChecksEnforce        []string `json:"registry_checks_enforce,omitempty"`
	StatusPolicy                 string   `json:"status_policy"`
	SignaturePolicy              string   `json:"signature_policy"`
	RepairHintPolicy             string   `json:"repair_hint_policy"`
}

func (p *AdmissionProfile) normalize() {
	if p.AcceptedBundleArtifact == "" {
		p.AcceptedBundleArtifact = p.AcceptedBundleArtifactType
	}
	if len(p.RequiredCertificateArtifacts) == 0 {
		p.RequiredCertificateArtifacts = p.RequiredCertificateArtifactTypes
	}
	if len(p.RequiredRegistryChecks) == 0 {
		p.RequiredRegistryChecks = p.RegistryChecksEnforce
	}
	if len(p.RequiredHandoffKinds) == 0 && strings.TrimSpace(p.RequiredHandoffKind) != "" {
		p.RequiredHandoffKinds = []string{p.RequiredHandoffKind}
	}
	if len(p.RequiredHandoffKinds) > 0 && p.RequiredHandoffKind == "" {
		p.RequiredHandoffKind = p.RequiredHandoffKinds[0]
	}
}

// IsToolUseProfile reports whether this profile targets tool-use bundles.
func (p *AdmissionProfile) IsToolUseProfile() bool {
	if p == nil {
		return false
	}
	p.normalize()
	return p.AcceptedBundleArtifact == "ToolUseScienceClaimBundle.v0"
}

// AdmissionProfileFromEnv loads PF_ADMISSION_PROFILE when set.
func AdmissionProfileFromEnv() (*AdmissionProfile, error) {
	id := strings.TrimSpace(os.Getenv("PF_ADMISSION_PROFILE"))
	if id == "" {
		return nil, nil
	}
	return LoadAdmissionProfile(id)
}

// ResolveAdmissionProfile loads by explicit ref or PF_ADMISSION_PROFILE (not required by itself).
func ResolveAdmissionProfile(explicitRef string) (*AdmissionProfile, error) {
	ref := normalizeProfileRef(explicitRef)
	if ref != "" {
		return LoadAdmissionProfile(ref)
	}
	return AdmissionProfileFromEnv()
}

// ResolveAdmissionProfileForReleaseMode requires a profile when releaseMode is true.
func ResolveAdmissionProfileForReleaseMode(explicitRef string, releaseMode bool) (*AdmissionProfile, error) {
	if !releaseMode {
		return ResolveAdmissionProfile(explicitRef)
	}
	ref := normalizeProfileRef(explicitRef)
	if ref == "" {
		ref = normalizeProfileRef(os.Getenv("PF_ADMISSION_PROFILE"))
	}
	if ref == "" {
		return nil, fmt.Errorf("%s: --admission-profile is required in release mode (or set PF_ADMISSION_PROFILE)", FailureCodeMissingAdmissionProfile)
	}
	profile, err := LoadAdmissionProfile(ref)
	if err != nil {
		return nil, fmt.Errorf("%s: %w", FailureCodeUnknownAdmissionProfile, err)
	}
	return profile, nil
}

func normalizeProfileRef(ref string) string {
	ref = strings.TrimSpace(ref)
	ref = strings.TrimSuffix(ref, ".json")
	return ref
}

// LoadAdmissionProfile loads a built-in admission profile by id or filename stem.
func LoadAdmissionProfile(profileRef string) (*AdmissionProfile, error) {
	id := normalizeProfileRef(profileRef)
	if id == "" {
		return nil, fmt.Errorf("admission profile id is required")
	}
	candidates := []string{
		"admission_profiles/" + id + ".json",
		"admission_profiles/" + strings.ReplaceAll(id, ".", "_") + ".json",
		"admission_profiles/" + strings.ReplaceAll(id, "_", ".") + ".json",
	}
	var data []byte
	var err error
	for _, path := range candidates {
		data, err = admissionProfileFS.ReadFile(path)
		if err == nil {
			break
		}
	}
	if err != nil {
		return nil, fmt.Errorf("%s: profile %q not found in built-in admission_profiles", FailureCodeUnknownAdmissionProfile, id)
	}
	var profile AdmissionProfile
	if err := json.Unmarshal(data, &profile); err != nil {
		return nil, fmt.Errorf("parse admission profile %q: %w", id, err)
	}
	profile.normalize()
	if profile.ProfileID == "" {
		profile.ProfileID = id
	}
	if err := ValidateAdmissionProfile(&profile); err != nil {
		return nil, err
	}
	return &profile, nil
}

// ValidateAdmissionProfile checks profile shape.
func ValidateAdmissionProfile(p *AdmissionProfile) error {
	if p == nil {
		return fmt.Errorf("admission profile is nil")
	}
	p.normalize()
	if strings.TrimSpace(p.ProfileID) == "" {
		return fmt.Errorf("admission profile missing profile_id")
	}
	if strings.TrimSpace(p.AcceptedBundleArtifact) == "" {
		return fmt.Errorf("admission profile %q missing accepted_bundle_artifact", p.ProfileID)
	}
	if len(p.RequiredHandoffKinds) == 0 {
		return fmt.Errorf("admission profile %q missing required_handoff_kinds", p.ProfileID)
	}
	if strings.TrimSpace(p.StatusPolicy) == "" {
		return fmt.Errorf("admission profile %q missing status_policy", p.ProfileID)
	}
	if strings.TrimSpace(p.SignaturePolicy) == "" {
		return fmt.Errorf("admission profile %q missing signature_policy", p.ProfileID)
	}
	if strings.TrimSpace(p.RepairHintPolicy) == "" {
		return fmt.Errorf("admission profile %q missing repair_hint_policy", p.ProfileID)
	}
	return nil
}

// EnforceAdmissionProfile validates bundle and handoff against profile rules.
func EnforceAdmissionProfile(profile *AdmissionProfile, bundlePath string, bundle *ScienceClaimBundle, handoff *LoadedHandoff) error {
	if profile == nil {
		return nil
	}
	profile.normalize()
	if profile.IsToolUseProfile() {
		return enforceAgentToolUseSafetyProfile(profile, bundlePath)
	}
	return enforceLabtrustQCProfile(profile, bundle, handoff)
}

func enforceLabtrustQCProfile(profile *AdmissionProfile, bundle *ScienceClaimBundle, handoff *LoadedHandoff) error {
	if bundle == nil {
		return fmt.Errorf("%s: profile %q requires a science claim bundle", FailureCodeReleaseModeBundleRequired, profile.ProfileID)
	}
	if profile.AcceptedBundleArtifact != "" && profile.AcceptedBundleArtifact != "ScienceClaimBundle.v0" {
		return fmt.Errorf("%s: profile %q accepts %s only", FailureCodeReleaseModeProfileRejected, profile.ProfileID, profile.AcceptedBundleArtifact)
	}
	if err := enforceProfileHandoff(profile, handoff); err != nil {
		return err
	}
	for _, rt := range profile.RequiredRuntimeArtifacts {
		if rt == "RuntimeReceipt.v0" && bundle.PrimaryRuntimeReceipt() == nil {
			return fmt.Errorf("%s: profile %q requires %s", FailureCodeReleaseModeCertificateRequired, profile.ProfileID, rt)
		}
	}
	if len(profile.RequiredCertificateArtifacts) == 0 {
		return nil
	}
	if len(bundle.Certificates) == 0 {
		return fmt.Errorf("%s: profile %q requires certificate types %v", FailureCodeReleaseModeCertificateRequired, profile.ProfileID, profile.RequiredCertificateArtifacts)
	}
	cert := firstCertificate(bundle)
	if cert == nil {
		return fmt.Errorf("%s: profile %q requires a certificate", FailureCodeReleaseModeCertificateRequired, profile.ProfileID)
	}
	for _, required := range profile.RequiredCertificateArtifacts {
		if required == "TraceCertificate.v0" {
			if strings.TrimSpace(cert.CertificateID) == "" {
				return fmt.Errorf("%s: profile %q requires TraceCertificate.v0", FailureCodeReleaseModeCertificateRequired, profile.ProfileID)
			}
			continue
		}
		return fmt.Errorf("%s: profile %q certificate type %q is not supported yet", FailureCodeReleaseModeProfileRejected, profile.ProfileID, required)
	}
	return nil
}

func enforceProfileHandoff(profile *AdmissionProfile, handoff *LoadedHandoff) error {
	allowed := profile.RequiredHandoffKinds
	if len(allowed) == 0 {
		allowed = []string{"bundle_to_verifier"}
	}
	if handoff == nil || (handoff.Manifest == nil && handoff.Legacy == nil) {
		return fmt.Errorf("%s: profile %q requires handoff kinds %v", FailureCodeReleaseModeHandoffRequired, profile.ProfileID, allowed)
	}
	if handoff.IsLegacy() {
		return fmt.Errorf("%s: profile %q forbids legacy pf_handoff.json", FailureCodeLegacyHandoffForbiddenInReleaseMode, profile.ProfileID)
	}
	if handoff.Manifest == nil {
		return fmt.Errorf("%s: profile %q requires HandoffManifest.v0", FailureCodeReleaseModeHandoffRequired, profile.ProfileID)
	}
	for _, kind := range allowed {
		if handoff.Manifest.HandoffKind == kind {
			return nil
		}
	}
	return fmt.Errorf("%s: profile %q requires handoff_kind in %v (got %q)", FailureCodeReleaseModeHandoffKindMismatch, profile.ProfileID, allowed, handoff.Manifest.HandoffKind)
}

// ValidateProfileRequiredRegistryChecks ensures profile-required registry semantics are satisfied in RCVR.
func ValidateProfileRequiredRegistryChecks(profile *AdmissionProfile, checks []ReleaseValidationCheck) error {
	if profile == nil || len(profile.RequiredRegistryChecks) == 0 {
		return nil
	}
	profile.normalize()
	byID := make(map[string]ReleaseValidationCheck, len(checks))
	for _, c := range checks {
		byID[c.CheckID] = c
	}
	for _, req := range profile.RequiredRegistryChecks {
		if profileRegistryCheckSatisfied(req, byID) {
			continue
		}
		return fmt.Errorf("%s: required registry check %q not satisfied in release chain result", ReasonRegistryAdmissionFailed, req)
	}
	return nil
}

func profileRegistryCheckSatisfied(req string, byID map[string]ReleaseValidationCheck) bool {
	aliases := []string{req}
	switch req {
	case "trace_hash_matches_runtime_receipt", "tool_trace_hash_matches_certificate":
		aliases = append(aliases, "trace_hash_consistent", "registry.TraceCertificate.v0.trace_hash_matches_runtime_receipt")
	case "certificate_id_consistency":
		aliases = append(aliases, "certificate_id_consistent")
	case "signed_input_bundle_hash_matches_certified":
		aliases = append(aliases, "signed_input_bundle_hash_match", "registry.SignedScienceClaimBundle.v0.signed_input_bundle_hash_matches_certified")
	case "tool_use_certificate_not_rejected":
		aliases = append(aliases, "tool_use_certificate_status")
	case "authorized_tool_calls_only":
		aliases = append(aliases, "tool_use_authorization")
	}
	for _, id := range aliases {
		c, ok := byID[id]
		if !ok {
			continue
		}
		if c.Status == "passed" {
			if exec, _ := c.Details["execution"].(string); exec == RegistryExecutionDeferred {
				allowed, _ := c.Details["release_mode_allowed"].(bool)
				return allowed
			}
			return true
		}
	}
	return false
}

// ProfileEnforcesRegistryCheck reports whether a release-chain check id must pass for this profile.
func (p *AdmissionProfile) ProfileEnforcesRegistryCheck(checkID string) bool {
	if p == nil {
		return false
	}
	p.normalize()
	for _, id := range p.RequiredRegistryChecks {
		if id == checkID {
			return true
		}
	}
	return false
}

// LoadAdmissionProfileFromPath loads profile JSON from an external file (for tests/overrides).
func LoadAdmissionProfileFromPath(path string) (*AdmissionProfile, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("%s: read %s: %w", FailureCodeUnknownAdmissionProfile, filepath.Base(resolved), err)
	}
	var profile AdmissionProfile
	if err := json.Unmarshal(data, &profile); err != nil {
		return nil, fmt.Errorf("%s: parse %s: %w", FailureCodeUnknownAdmissionProfile, filepath.Base(resolved), err)
	}
	profile.normalize()
	if err := ValidateAdmissionProfile(&profile); err != nil {
		return nil, err
	}
	return &profile, nil
}
