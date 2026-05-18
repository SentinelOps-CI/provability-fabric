// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"embed"
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

//go:embed admission_profiles/*.json
var admissionProfileFS embed.FS

// AdmissionProfile defines PF admission policy for a PCS workflow.
type AdmissionProfile struct {
	ProfileID                      string   `json:"profile_id"`
	Description                    string   `json:"description,omitempty"`
	AcceptedBundleArtifact         string   `json:"accepted_bundle_artifact"`
	AcceptedBundleArtifactType     string   `json:"accepted_bundle_artifact_type,omitempty"`
	RequiredCertificateArtifacts   []string `json:"required_certificate_artifacts"`
	RequiredCertificateArtifactTypes []string `json:"required_certificate_artifact_types,omitempty"`
	RequiredHandoffKind            string   `json:"required_handoff_kind"`
	RequiredRegistryChecks         []string `json:"required_registry_checks"`
	RegistryChecksEnforce          []string `json:"registry_checks_enforce,omitempty"`
	SignaturePolicy                string   `json:"signature_policy"`
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
}

// AdmissionProfileFromEnv loads PF_ADMISSION_PROFILE when set.
func AdmissionProfileFromEnv() (*AdmissionProfile, error) {
	id := strings.TrimSpace(os.Getenv("PF_ADMISSION_PROFILE"))
	if id == "" {
		return nil, nil
	}
	return LoadAdmissionProfile(id)
}

// ResolveAdmissionProfile loads by explicit id or PF_ADMISSION_PROFILE.
func ResolveAdmissionProfile(explicitID string) (*AdmissionProfile, error) {
	if strings.TrimSpace(explicitID) != "" {
		return LoadAdmissionProfile(explicitID)
	}
	return AdmissionProfileFromEnv()
}

// LoadAdmissionProfile loads a built-in admission profile by id.
func LoadAdmissionProfile(profileID string) (*AdmissionProfile, error) {
	id := strings.TrimSpace(profileID)
	if id == "" {
		return nil, fmt.Errorf("admission profile id is required")
	}
	var data []byte
	var err error
	for _, path := range []string{
		"admission_profiles/" + id + ".json",
		"admission_profiles/" + strings.ReplaceAll(id, ".", "_") + ".json",
	} {
		data, err = admissionProfileFS.ReadFile(path)
		if err == nil {
			break
		}
	}
	if err != nil {
		return nil, fmt.Errorf("unknown admission profile %q", id)
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
	if strings.TrimSpace(p.RequiredHandoffKind) == "" {
		return fmt.Errorf("admission profile %q missing required_handoff_kind", p.ProfileID)
	}
	if strings.TrimSpace(p.SignaturePolicy) == "" {
		return fmt.Errorf("admission profile %q missing signature_policy", p.ProfileID)
	}
	return nil
}

// EnforceAdmissionProfile validates bundle and handoff against profile rules.
func EnforceAdmissionProfile(profile *AdmissionProfile, bundle *ScienceClaimBundle, handoff *LoadedHandoff) error {
	if profile == nil {
		return nil
	}
	profile.normalize()
	if bundle == nil {
		return fmt.Errorf("%s: admission profile requires a science claim bundle", FailureCodeReleaseModeBundleRequired)
	}
	if profile.AcceptedBundleArtifact != "" && profile.AcceptedBundleArtifact != "ScienceClaimBundle.v0" {
		return fmt.Errorf("%s: profile %q accepts %s only", FailureCodeReleaseModeProfileRejected, profile.ProfileID, profile.AcceptedBundleArtifact)
	}
	if err := enforceProfileHandoff(profile, handoff); err != nil {
		return err
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
	kind := profile.RequiredHandoffKind
	if kind == "" || kind == "HandoffManifest.v0" {
		kind = "bundle_to_verifier"
	}
	if handoff == nil || (handoff.Manifest == nil && handoff.Legacy == nil) {
		return fmt.Errorf("%s: profile %q requires handoff kind %q", FailureCodeReleaseModeHandoffRequired, profile.ProfileID, kind)
	}
	if handoff.IsLegacy() {
		return fmt.Errorf("%s: profile %q forbids legacy pf_handoff.json", FailureCodeLegacyHandoffForbiddenInReleaseMode, profile.ProfileID)
	}
	if handoff.Manifest == nil {
		return fmt.Errorf("%s: profile %q requires HandoffManifest.v0", FailureCodeReleaseModeHandoffRequired, profile.ProfileID)
	}
	if kind != "" && handoff.Manifest.HandoffKind != kind {
		return fmt.Errorf("%s: profile %q requires handoff_kind %q (got %q)", FailureCodeReleaseModeHandoffKindMismatch, profile.ProfileID, kind, handoff.Manifest.HandoffKind)
	}
	return nil
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
		if satisfied := profileRegistryCheckSatisfied(req, byID); satisfied {
			continue
		}
		return fmt.Errorf("%s: required registry check %q not satisfied in release chain result", ReasonRegistryAdmissionFailed, req)
	}
	return nil
}

func profileRegistryCheckSatisfied(req string, byID map[string]ReleaseValidationCheck) bool {
	aliases := []string{req}
	switch req {
	case "trace_hash_matches_runtime_receipt":
		aliases = append(aliases, "trace_hash_consistent", "registry.TraceCertificate.v0.trace_hash_matches_runtime_receipt")
	case "certificate_id_consistency":
		aliases = append(aliases, "certificate_id_consistent")
	case "signed_input_bundle_hash_matches_certified":
		aliases = append(aliases, "signed_input_bundle_hash_match", "registry.SignedScienceClaimBundle.v0.signed_input_bundle_hash_matches_certified")
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
