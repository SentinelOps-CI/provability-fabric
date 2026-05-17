// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"path/filepath"
	"strings"
	"time"
)

// ReleaseValidationCheck is a pcs-core release_validation_check entry.
type ReleaseValidationCheck struct {
	CheckID     string         `json:"check_id"`
	Description string         `json:"description"`
	Status      string         `json:"status"`
	Details     map[string]any `json:"details"`
}

// ReleaseChainValidationResult is ReleaseChainValidationResult.v0 emitted by PF.
type ReleaseChainValidationResult struct {
	SchemaVersion     string                   `json:"schema_version"`
	ValidationID      string                   `json:"validation_id"`
	ReleaseID         string                   `json:"release_id"`
	ReleaseCandidate  string                   `json:"release_candidate"`
	Validator         string                   `json:"validator"`
	ValidatorVersion  string                   `json:"validator_version"`
	CheckedAt         string                   `json:"checked_at"`
	Status            string                   `json:"status"`
	Checks            []ReleaseValidationCheck   `json:"checks"`
	ArtifactsChecked  int                      `json:"artifacts_checked"`
	FailureCodes      []string                 `json:"failure_codes"`
	SourceRepo        string                   `json:"source_repo"`
	SourceCommit      string                   `json:"source_commit"`
	SignatureOrDigest string                   `json:"signature_or_digest"`
}

// ReleaseChainVerifyOptions configures release-chain validation.
type ReleaseChainVerifyOptions struct {
	RepoRoot          string
	ArtifactDir       string
	ValidatorVersion  string
	SourceCommit      string
	ReleaseMode       bool
}

// VerifyReleaseChainFromManifest validates manifest artifact pins in the manifest directory.
func VerifyReleaseChainFromManifest(manifestPath string, opts ReleaseChainVerifyOptions) (ReleaseChainValidationResult, error) {
	resolved, err := ResolveArtifactPath(manifestPath)
	if err != nil {
		return ReleaseChainValidationResult{}, err
	}
	manifest, err := LoadReleaseManifest(resolved)
	if err != nil {
		return ReleaseChainValidationResult{}, err
	}
	if err := ValidateReleaseManifestFile(opts.RepoRoot, resolved); err != nil {
		return buildReleaseChainResult(manifest, nil, []string{"PCS_SCHEMA_INVALID"}, opts, err)
	}
	baseDir := opts.ArtifactDir
	if strings.TrimSpace(baseDir) == "" {
		baseDir = filepath.Dir(resolved)
	}
	checks, failureCodes := validateManifestArtifacts(baseDir, manifest)
	return buildReleaseChainResult(manifest, checks, failureCodes, opts, nil)
}

// PFReleaseChainArtifactNames returns manifest artifact filenames PF validates at admission.
func PFReleaseChainArtifactNames(manifest *ReleaseManifest) []string {
	return pfReleaseChainArtifactNames(manifest)
}

// pfReleaseChainArtifactNames returns manifest artifact filenames PF validates at admission.
// Scientific Memory import reports are downstream of PF signing and may use a separate pin.
func pfReleaseChainArtifactNames(manifest *ReleaseManifest) []string {
	if manifest == nil {
		return nil
	}
	names := make([]string, 0, len(manifest.Artifacts))
	for name := range manifest.Artifacts {
		if isDownstreamOfPFAdmission(name) {
			continue
		}
		names = append(names, name)
	}
	return names
}

func isDownstreamOfPFAdmission(artifactName string) bool {
	return artifactName == "scientific_memory_import_report.json"
}

func validateManifestArtifacts(baseDir string, manifest *ReleaseManifest) ([]ReleaseValidationCheck, []string) {
	var checks []ReleaseValidationCheck
	var failureCodes []string
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		checkID := "manifest_artifact_" + sanitizeCheckID(name)
		path := filepath.Join(baseDir, name)
		digest, err := FileDigest(path)
		if err != nil {
			checks = append(checks, releaseFailCheck(checkID,
				fmt.Sprintf("Artifact %s is present and matches registry sha256", name),
				"PCS_ARTIFACT_MISSING", map[string]any{"artifact": name, "error": err.Error()}))
			failureCodes = append(failureCodes, "PCS_ARTIFACT_MISSING")
			continue
		}
		if digest != entry.SHA256 {
			checks = append(checks, releaseFailCheck(checkID,
				fmt.Sprintf("Artifact %s is present and matches registry sha256", name),
				"PCS_MANIFEST_HASH_MISMATCH",
				map[string]any{"artifact": name, "expected": entry.SHA256, "actual": digest}))
			failureCodes = append(failureCodes, "PCS_MANIFEST_HASH_MISMATCH")
			continue
		}
		checks = append(checks, releasePassCheck(checkID,
			fmt.Sprintf("Artifact %s is present and matches registry sha256", name),
			map[string]any{"artifact": name, "sha256": digest}))
	}
	if len(checks) == 0 {
		checks = append(checks, releasePassCheck("manifest_artifacts", "Release manifest lists artifacts", map[string]any{}))
	}
	for _, name := range manifestArtifactsDownstream(manifest) {
		checks = append(checks, releaseSkipCheck(
			"manifest_artifact_"+sanitizeCheckID(name)+"_downstream",
			fmt.Sprintf("Artifact %s is validated downstream of PF admission", name),
			map[string]any{"artifact": name},
		))
	}
	return checks, uniqueStrings(failureCodes)
}

func manifestArtifactsDownstream(manifest *ReleaseManifest) []string {
	if manifest == nil {
		return nil
	}
	var names []string
	for name := range manifest.Artifacts {
		if isDownstreamOfPFAdmission(name) {
			names = append(names, name)
		}
	}
	return names
}

func releaseSkipCheck(id, description string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return ReleaseValidationCheck{CheckID: id, Description: description, Status: "skipped", Details: details}
}

func buildReleaseChainResult(
	manifest *ReleaseManifest,
	checks []ReleaseValidationCheck,
	failureCodes []string,
	opts ReleaseChainVerifyOptions,
	schemaErr error,
) (ReleaseChainValidationResult, error) {
	if manifest == nil {
		return ReleaseChainValidationResult{}, fmt.Errorf("release manifest is nil")
	}
	if schemaErr != nil {
		checks = []ReleaseValidationCheck{releaseFailCheck("release_manifest_schema",
			"Release manifest matches pcs-core JSON Schema",
			"PCS_SCHEMA_INVALID", map[string]any{"error": schemaErr.Error()})}
		failureCodes = []string{"PCS_SCHEMA_INVALID"}
	}
	if len(checks) == 0 {
		checks = []ReleaseValidationCheck{releasePassCheck("release_chain", "Release chain validation", map[string]any{})}
	}
	status := StatusProofChecked
	if len(failureCodes) > 0 {
		status = StatusRejected
	}
	for _, c := range checks {
		if c.Status == "failed" {
			status = StatusRejected
		}
	}
	ver := opts.ValidatorVersion
	if ver == "" {
		ver = DefaultVerifierVersion
	}
	sourceCommit := opts.SourceCommit
	if sourceCommit == "" {
		sourceCommit = ResolveSourceCommit()
	}
	checkedAt := time.Now().UTC().Format(time.RFC3339)
	if DeterministicMode() {
		checkedAt = "2026-05-17T17:01:22Z"
	}
	if failureCodes == nil {
		failureCodes = []string{}
	}
	result := ReleaseChainValidationResult{
		SchemaVersion:    SchemaVersionV0,
		ValidationID:     "validation-" + manifest.ReleaseID,
		ReleaseID:        manifest.ReleaseID,
		ReleaseCandidate: manifest.ReleaseCandidate,
		Validator:        VerifierName,
		ValidatorVersion: ver,
		CheckedAt:        checkedAt,
		Status:           status,
		Checks:           checks,
		ArtifactsChecked: len(pfReleaseChainArtifactNames(manifest)),
		FailureCodes:     failureCodes,
		SourceRepo:       VerifierSourceRepo,
		SourceCommit:     sourceCommit,
	}
	result.SignatureOrDigest = digestReleaseChainValidationResult(result)
	if err := ValidateReleaseChainValidationResult(opts.RepoRoot, result); err != nil {
		return result, fmt.Errorf("release chain validation result schema: %w", err)
	}
	if err := ValidateReleaseChainValidationResultSemantics(&result); err != nil {
		return result, fmt.Errorf("release chain validation result semantics: %w", err)
	}
	return result, nil
}

// BuildReleaseChainValidationResultFromVerification maps a bundle verification into RCVR for single-bundle admission.
func BuildReleaseChainValidationResultFromVerification(
	manifest *ReleaseManifest,
	bundleResult VerificationResult,
	handoff *HandoffManifest,
	opts ReleaseChainVerifyOptions,
) (ReleaseChainValidationResult, error) {
	var checks []ReleaseValidationCheck
	var failureCodes []string

	if manifest != nil {
		checks = append(checks, releasePassCheck("release_manifest_loaded",
			"Release manifest loaded for admission", map[string]any{
				"release_id":        manifest.ReleaseID,
				"release_candidate": manifest.ReleaseCandidate,
			}))
	}
	if handoff != nil {
		id := "handoff_manifest_validated"
		if handoff.Status == HandoffStatusValidated &&
			handoff.FromComponent == ComponentLabTrustGym &&
			handoff.ToComponent == ComponentProvabilityFabric {
			checks = append(checks, releasePassCheck(id, "HandoffManifest.v0 targets Provability Fabric with Validated status",
				map[string]any{"handoff_id": handoff.HandoffID}))
		} else {
			checks = append(checks, releaseFailCheck(id, "HandoffManifest.v0 targets Provability Fabric with Validated status",
				"PCS_HANDOFF_INVALID", map[string]any{"status": handoff.Status}))
			failureCodes = append(failureCodes, "PCS_HANDOFF_INVALID")
		}
	}
	vrCheck := "science_claim_bundle_verification"
	if bundleResult.Status == StatusProofChecked {
		checks = append(checks, releasePassCheck(vrCheck,
			"ScienceClaimBundle verification reached ProofChecked",
			map[string]any{"verification_id": bundleResult.VerificationID}))
	} else {
		checks = append(checks, releaseFailCheck(vrCheck,
			"ScienceClaimBundle verification reached ProofChecked",
			"PCS_VERIFICATION_REJECTED", map[string]any{"status": bundleResult.Status}))
		failureCodes = append(failureCodes, "PCS_VERIFICATION_REJECTED")
		for _, c := range FailedChecks(bundleResult) {
			if code, ok := c.Details["reason_code"].(string); ok && code != "" {
				failureCodes = append(failureCodes, code)
			}
		}
	}
	failureCodes = uniqueStrings(failureCodes)
	return buildReleaseChainResult(manifest, checks, failureCodes, opts, nil)
}

func releasePassCheck(id, description string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return ReleaseValidationCheck{CheckID: id, Description: description, Status: "passed", Details: details}
}

func releaseFailCheck(id, description, failureCode string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	details["failure_code"] = failureCode
	return ReleaseValidationCheck{CheckID: id, Description: description, Status: "failed", Details: details}
}

func sanitizeCheckID(name string) string {
	out := strings.Map(func(r rune) rune {
		switch {
		case r >= 'a' && r <= 'z', r >= 'A' && r <= 'Z', r >= '0' && r <= '9':
			return r
		default:
			return '_'
		}
	}, name)
	return strings.Trim(out, "_")
}

func uniqueStrings(in []string) []string {
	seen := make(map[string]struct{}, len(in))
	var out []string
	for _, s := range in {
		if s == "" {
			continue
		}
		if _, ok := seen[s]; ok {
			continue
		}
		seen[s] = struct{}{}
		out = append(out, s)
	}
	return out
}

func digestReleaseChainValidationResult(result ReleaseChainValidationResult) string {
	copy := result
	copy.SignatureOrDigest = ""
	raw, err := json.Marshal(copy)
	if err != nil {
		return ""
	}
	var doc map[string]any
	if err := json.Unmarshal(raw, &doc); err != nil {
		return ""
	}
	digest, err := CanonicalHash(doc)
	if err != nil {
		return ""
	}
	return digest
}
