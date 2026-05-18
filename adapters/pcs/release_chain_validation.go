// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// Release validation check IDs emitted by PF release-chain admission.
var RequiredReleaseChainCheckIDs = []string{
	"manifest_hashes_match",
	"producer_commits_match",
	"certificate_id_consistent",
	"trace_hash_consistent",
	"signed_input_bundle_hash_match",
	"scientific_memory_import_passed",
	"registry_artifact_registered",
	"registry_schema_matches",
	"registry_producer_allowed",
	"registry_status_allowed",
	"registry_required_fields_present",
	"registry_semantic_checks_executed",
	"registry_admission_passed",
}

// ReleaseValidationCheck is a pcs-core release_validation_check entry.
type ReleaseValidationCheck struct {
	CheckID           string         `json:"check_id"`
	Description       string         `json:"description"`
	Status            string         `json:"status"`
	Details           map[string]any `json:"details"`
	RegistryCheckRefs []string       `json:"registry_check_refs"`
}

// ReleaseChainValidationResult is ReleaseChainValidationResult.v0 emitted by PF.
type ReleaseChainValidationResult struct {
	SchemaVersion     string                 `json:"schema_version"`
	ValidationID      string                 `json:"validation_id"`
	ReleaseID         string                 `json:"release_id"`
	ReleaseCandidate  string                 `json:"release_candidate"`
	Validator         string                 `json:"validator"`
	ValidatorVersion  string                 `json:"validator_version"`
	CheckedAt         string                 `json:"checked_at"`
	Status            string                 `json:"status"`
	Checks            []ReleaseValidationCheck `json:"checks"`
	ArtifactsChecked  int                    `json:"artifacts_checked"`
	FailureCodes      []string               `json:"failure_codes"`
	SourceRepo        string                 `json:"source_repo"`
	SourceCommit      string                 `json:"source_commit"`
	SignatureOrDigest string                 `json:"signature_or_digest"`
}

// ReleaseChainVerifyOptions configures release-chain validation.
type ReleaseChainVerifyOptions struct {
	RepoRoot                      string
	ArtifactDir                   string
	ValidatorVersion              string
	SourceCommit                  string
	ReleaseMode                   bool
	Registry                      *ArtifactRegistry
	AllowSkippedRegistrySemantics bool
	AdmissionProfile              *AdmissionProfile
}

// VerifyReleaseChainFromManifest validates manifest artifact pins and registry admission.
func VerifyReleaseChainFromManifest(manifestPath string, opts ReleaseChainVerifyOptions) (ReleaseChainValidationResult, error) {
	if err := EnforceReleaseChainAdmission(ReleaseAdmissionPolicy{
		ReleaseMode:                   opts.ReleaseMode,
		AllowSkippedRegistrySemantics: opts.AllowSkippedRegistrySemantics,
	}, manifestPath, opts.Registry); err != nil {
		return ReleaseChainValidationResult{}, err
	}
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
	checks, failureCodes := runReleaseChainChecks(baseDir, manifest, opts)
	return buildReleaseChainResult(manifest, checks, failureCodes, opts, nil)
}

// PFReleaseChainArtifactNames returns manifest artifact filenames PF validates at admission.
func PFReleaseChainArtifactNames(manifest *ReleaseManifest) []string {
	return pfReleaseChainArtifactNames(manifest)
}

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

func runReleaseChainChecks(baseDir string, manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) ([]ReleaseValidationCheck, []string) {
	byID := make(map[string]ReleaseValidationCheck)
	var failureCodes []string

	hashCheck, hashFailures := checkManifestHashesMatch(baseDir, manifest)
	byID["manifest_hashes_match"] = hashCheck
	failureCodes = append(failureCodes, hashFailures...)

	commitCheck, commitFailures := checkProducerCommitsMatch(manifest, opts.ReleaseMode)
	byID["producer_commits_match"] = commitCheck
	failureCodes = append(failureCodes, commitFailures...)

	certCheck, certFailures := checkCertificateIDConsistent(baseDir, manifest)
	byID["certificate_id_consistent"] = certCheck
	failureCodes = append(failureCodes, certFailures...)

	traceCheck, traceFailures := checkTraceHashConsistent(baseDir, manifest)
	byID["trace_hash_consistent"] = traceCheck
	failureCodes = append(failureCodes, traceFailures...)

	signedCheck, signedFailures := checkSignedInputBundleHashMatch(baseDir, manifest)
	byID["signed_input_bundle_hash_match"] = signedCheck
	failureCodes = append(failureCodes, signedFailures...)

	smCheck, smFailures := checkScientificMemoryImportPassed(baseDir, manifest, opts)
	byID["scientific_memory_import_passed"] = smCheck
	failureCodes = append(failureCodes, smFailures...)

	for id, c := range runRegistryReleaseChainChecks(manifest, opts) {
		byID[id] = c
		if c.Status == "failed" {
			if fc, ok := c.Details["failure_code"].(string); ok && fc != "" {
				failureCodes = append(failureCodes, fc)
			}
		}
	}

	regCheck, regFailures := checkRegistryAdmissionPassed(manifest, opts)
	byID["registry_admission_passed"] = regCheck
	failureCodes = append(failureCodes, regFailures...)

	checks := normalizeReleaseChainChecks(byID)
	auditCtx := RegistrySemanticAuditContext{
		Manifest: manifest,
		Registry: opts.Registry,
		BaseDir:  baseDir,
		Bundle:   loadCertifiedBundleForAudit(baseDir),
		Opts: RegistryValidateOptions{
			ReleaseMode:                   opts.ReleaseMode,
			AllowSkippedRegistrySemantics: opts.AllowSkippedRegistrySemantics,
		},
	}
	registrySemantic := CollectRegistrySemanticChecks(auditCtx)
	checks = append(checks, registrySemantic...)
	byID["registry_semantic_checks_executed"] = summarizeRegistrySemanticChecksExecuted(registrySemantic, opts)
	for _, c := range registrySemantic {
		if c.Status == "failed" {
			if fc, ok := c.Details["failure_code"].(string); ok && fc != "" {
				failureCodes = append(failureCodes, fc)
			} else {
				failureCodes = append(failureCodes, ReasonRegistryAdmissionFailed)
			}
		}
	}
	if hasUnexplainedDeferredRegistryCheck(checks, opts.ReleaseMode, opts.AllowSkippedRegistrySemantics) {
		byID["registry_semantic_checks_executed"] = releaseFailCheck("registry_semantic_checks_executed",
			registryCheckDescription("registry_semantic_checks_executed"),
			ReasonRegistryAdmissionFailed,
			map[string]any{"error": "unexplained deferred registry semantic check in release mode"})
		failureCodes = append(failureCodes, ReasonRegistryAdmissionFailed)
		checks = replaceCheck(checks, byID["registry_semantic_checks_executed"])
	}
	if err := ValidateRegistrySemanticChecksPresent(auditCtx, checks); err != nil && opts.ReleaseMode && !opts.AllowSkippedRegistrySemantics {
		byID["registry_semantic_checks_executed"] = releaseFailCheck("registry_semantic_checks_executed",
			registryCheckDescription("registry_semantic_checks_executed"),
			FailureCodeRegistryCheckNotInResult,
			map[string]any{"error": err.Error()})
		failureCodes = append(failureCodes, FailureCodeRegistryCheckNotInResult)
		checks = replaceCheck(checks, byID["registry_semantic_checks_executed"])
	}
	return checks, uniqueStrings(failureCodes)
}

func replaceCheck(checks []ReleaseValidationCheck, updated ReleaseValidationCheck) []ReleaseValidationCheck {
	for i, c := range checks {
		if c.CheckID == updated.CheckID {
			checks[i] = updated
			return checks
		}
	}
	return append(checks, updated)
}

func summarizeRegistrySemanticChecksExecuted(registrySemantic []ReleaseValidationCheck, opts ReleaseChainVerifyOptions) ReleaseValidationCheck {
	const id = "registry_semantic_checks_executed"
	if opts.Registry == nil {
		return releaseSkipCheck(id, registryCheckDescription(id), map[string]any{"message": "registry not provided"})
	}
	if len(registrySemantic) == 0 {
		return releasePassCheck(id, registryCheckDescription(id), map[string]any{"registry_semantic_checks": 0})
	}
	var failed, deferred int
	for _, c := range registrySemantic {
		switch c.Status {
		case "failed":
			failed++
		case "passed":
			if exec, _ := c.Details["execution"].(string); exec == RegistryExecutionDeferred {
				deferred++
			}
		}
	}
	if failed > 0 {
		return releaseFailCheck(id, registryCheckDescription(id),
			ReasonRegistryAdmissionFailed,
			map[string]any{"failed_registry_semantic_checks": failed, "deferred_registry_semantic_checks": deferred})
	}
	return releasePassCheck(id, registryCheckDescription(id),
		map[string]any{
			"registry_semantic_checks":          len(registrySemantic),
			"deferred_registry_semantic_checks": deferred,
		})
}

func normalizeReleaseChainChecks(byID map[string]ReleaseValidationCheck) []ReleaseValidationCheck {
	out := make([]ReleaseValidationCheck, 0, len(RequiredReleaseChainCheckIDs))
	for _, id := range RequiredReleaseChainCheckIDs {
		if c, ok := byID[id]; ok {
			out = append(out, c)
			continue
		}
		out = append(out, releaseSkipCheck(id, "check not evaluated", map[string]any{}))
	}
	return out
}

func checkManifestHashesMatch(baseDir string, manifest *ReleaseManifest) (ReleaseValidationCheck, []string) {
	var mismatches []map[string]any
	for _, name := range pfReleaseChainArtifactNames(manifest) {
		entry := manifest.Artifacts[name]
		path := filepath.Join(baseDir, name)
		digest, err := FileDigest(path)
		if err != nil {
			mismatches = append(mismatches, map[string]any{"artifact": name, "error": err.Error()})
			continue
		}
		if digest != entry.SHA256 {
			mismatches = append(mismatches, map[string]any{"artifact": name, "expected": entry.SHA256, "actual": digest})
		}
	}
	if len(mismatches) > 0 {
		details := map[string]any{"mismatches": mismatches}
		if len(mismatches) == 1 {
			if art, ok := mismatches[0]["artifact"].(string); ok {
				details["artifact_path"] = art
			}
			details["expected"] = mismatches[0]["expected"]
			details["actual"] = mismatches[0]["actual"]
		}
		return releaseFailCheck("manifest_hashes_match",
			"All manifest artifact hashes match on-disk files",
			"PCS_MANIFEST_HASH_MISMATCH",
			details), []string{"PCS_MANIFEST_HASH_MISMATCH"}
	}
	return releasePassCheck("manifest_hashes_match",
		"All manifest artifact hashes match on-disk files",
		map[string]any{"artifacts_checked": len(pfReleaseChainArtifactNames(manifest))}), nil
}

func checkProducerCommitsMatch(manifest *ReleaseManifest, releaseMode bool) (ReleaseValidationCheck, []string) {
	if !releaseMode {
		return releasePassCheck("producer_commits_match",
			"Producer repository commits satisfy release policy",
			map[string]any{"release_mode": false}), nil
	}
	if err := ValidateReleaseManifestSemantics(manifest); err != nil {
		return releaseFailCheck("producer_commits_match",
			"Producer repository commits satisfy release policy",
			"PCS_SOURCE_COMMIT_PLACEHOLDER",
			map[string]any{"error": err.Error()}), []string{"PCS_SOURCE_COMMIT_PLACEHOLDER"}
	}
	return releasePassCheck("producer_commits_match",
		"Producer repository commits satisfy release policy",
		map[string]any{"producer_repos": len(manifest.ProducerRepos)}), nil
}

func checkCertificateIDConsistent(baseDir string, manifest *ReleaseManifest) (ReleaseValidationCheck, []string) {
	certID, err := loadReleaseChainCertificateID(baseDir)
	if err != nil {
		return releaseFailCheck("certificate_id_consistent",
			"Certificate ID is identical across certificate, certified bundle, verification result, and signed bundle",
			"PCS_CERTIFICATE_ID_MISMATCH",
			map[string]any{"error": err.Error()}), []string{"PCS_CERTIFICATE_ID_MISMATCH"}
	}
	details := map[string]any{"certificate_id": certID}
	if vrPath := filepath.Join(baseDir, "verification_result.json"); fileExists(vrPath) {
		vr, err := loadVerificationResultFile(vrPath)
		if err == nil && vr.VerifiedInput != nil && vr.VerifiedInput.CertificateID != certID {
			return releaseFailCheck("certificate_id_consistent",
				"Certificate ID is identical across certificate, certified bundle, verification result, and signed bundle",
				"PCS_CERTIFICATE_ID_MISMATCH",
				map[string]any{
					"certificate_id":      certID,
					"verification_result": vr.VerifiedInput.CertificateID,
					"artifact_path":       "science_claim_bundle.certified.json",
					"expected":            certID,
					"actual":              vr.VerifiedInput.CertificateID,
					"responsible_component": ComponentLabTrustGym,
				}), []string{"PCS_CERTIFICATE_ID_MISMATCH"}
		}
	}
	return releasePassCheck("certificate_id_consistent",
		"Certificate ID is identical across certificate, certified bundle, verification result, and signed bundle",
		details), nil
}

func checkTraceHashConsistent(baseDir string, manifest *ReleaseManifest) (ReleaseValidationCheck, []string) {
	traceHash, err := loadReleaseChainTraceHash(baseDir)
	if err != nil {
		return releaseFailCheck("trace_hash_consistent",
			"Trace hash is identical across runtime receipt, certificate, and verification result",
			"PCS_TRACE_HASH_MISMATCH",
			map[string]any{"error": err.Error()}), []string{"PCS_TRACE_HASH_MISMATCH"}
	}
	if vrPath := filepath.Join(baseDir, "verification_result.json"); fileExists(vrPath) {
		vr, err := loadVerificationResultFile(vrPath)
		if err == nil && vr.VerifiedInput != nil && vr.VerifiedInput.TraceHash != "" && vr.VerifiedInput.TraceHash != traceHash {
			return releaseFailCheck("trace_hash_consistent",
				"Trace hash is identical across runtime receipt, certificate, and verification result",
				"PCS_TRACE_HASH_MISMATCH",
				map[string]any{"bundle_trace_hash": traceHash, "verification_result": vr.VerifiedInput.TraceHash}), []string{"PCS_TRACE_HASH_MISMATCH"}
		}
	}
	return releasePassCheck("trace_hash_consistent",
		"Trace hash is identical across runtime receipt, certificate, and verification result",
		map[string]any{"trace_hash": traceHash}), nil
}

func checkSignedInputBundleHashMatch(baseDir string, manifest *ReleaseManifest) (ReleaseValidationCheck, []string) {
	signedPath := filepath.Join(baseDir, "signed_science_claim_bundle.json")
	if !fileExists(signedPath) {
		return releaseSkipCheck("signed_input_bundle_hash_match",
			"Signed bundle signed_input_bundle_hash matches certified bundle file digest",
			map[string]any{"message": "signed_science_claim_bundle.json not present"}), nil
	}
	signed, err := LoadSignedScienceClaimBundle(signedPath)
	if err != nil {
		return releaseFailCheck("signed_input_bundle_hash_match",
			"Signed bundle signed_input_bundle_hash matches certified bundle file digest",
			"PCS_SIGNED_INPUT_HASH_MISMATCH",
			map[string]any{"error": err.Error()}), []string{"PCS_SIGNED_INPUT_HASH_MISMATCH"}
	}
	certPath := filepath.Join(baseDir, "science_claim_bundle.certified.json")
	want, err := FileDigest(certPath)
	if err != nil {
		return releaseFailCheck("signed_input_bundle_hash_match",
			"Signed bundle signed_input_bundle_hash matches certified bundle file digest",
			"PCS_ARTIFACT_MISSING",
			map[string]any{"error": err.Error()}), []string{"PCS_ARTIFACT_MISSING"}
	}
	if signed.SignedInputBundleHash != want {
		return releaseFailCheck("signed_input_bundle_hash_match",
			"Signed bundle signed_input_bundle_hash matches certified bundle file digest",
			"PCS_SIGNED_INPUT_HASH_MISMATCH",
			map[string]any{"expected": want, "actual": signed.SignedInputBundleHash}), []string{"PCS_SIGNED_INPUT_HASH_MISMATCH"}
	}
	return releasePassCheck("signed_input_bundle_hash_match",
		"Signed bundle signed_input_bundle_hash matches certified bundle file digest",
		map[string]any{"signed_input_bundle_hash": signed.SignedInputBundleHash}), nil
}

func checkScientificMemoryImportPassed(baseDir string, manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	const name = "scientific_memory_import_report.json"
	entry, inManifest := manifest.Artifacts[name]
	if !inManifest {
		return releasePassCheck("scientific_memory_import_passed",
			"Scientific Memory import report validated or downstream of PF admission",
			map[string]any{"message": "not listed in release manifest"}), nil
	}
	if isDownstreamOfPFAdmission(name) {
		path := filepath.Join(baseDir, name)
		if !fileExists(path) {
			if opts.ReleaseMode && !opts.AllowSkippedRegistrySemantics {
				return releaseFailCheck("scientific_memory_import_passed",
					"Scientific Memory import report validated when pinned in manifest",
					"PCS_ARTIFACT_MISSING",
					map[string]any{"artifact": name, "message": "downstream artifact pinned but file missing in release mode"}), []string{"PCS_ARTIFACT_MISSING"}
			}
			return releasePassCheck("scientific_memory_import_passed",
				"Scientific Memory import report validated downstream of PF admission",
				map[string]any{"artifact": name, "downstream": true}), nil
		}
		digest, err := FileDigest(path)
		if err != nil {
			return releaseFailCheck("scientific_memory_import_passed",
				"Scientific Memory import report hash matches manifest pin",
				"PCS_ARTIFACT_MISSING",
				map[string]any{"error": err.Error()}), []string{"PCS_ARTIFACT_MISSING"}
		}
		if digest != entry.SHA256 {
			return releaseFailCheck("scientific_memory_import_passed",
				"Scientific Memory import report hash matches manifest pin",
				"PCS_MANIFEST_HASH_MISMATCH",
				map[string]any{"expected": entry.SHA256, "actual": digest}), []string{"PCS_MANIFEST_HASH_MISMATCH"}
		}
		return releasePassCheck("scientific_memory_import_passed",
			"Scientific Memory import report hash matches manifest pin",
			map[string]any{"artifact": name, "sha256": digest}), nil
	}
	return releasePassCheck("scientific_memory_import_passed",
		"Scientific Memory import report validated",
		map[string]any{}), nil
}

func checkRegistryAdmissionPassed(manifest *ReleaseManifest, opts ReleaseChainVerifyOptions) (ReleaseValidationCheck, []string) {
	if opts.Registry == nil {
		if opts.ReleaseMode {
			return releaseFailCheck("registry_admission_passed",
				"Release manifest artifacts satisfy ArtifactRegistry.v0",
				"PCS_REGISTRY_ADMISSION_FAILED",
				map[string]any{"error": "registry not provided"}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
		}
		return releaseSkipCheck("registry_admission_passed",
			"Release manifest artifacts satisfy ArtifactRegistry.v0",
			map[string]any{"message": "registry not provided"}), nil
	}
	regOpts := RegistryValidateOptions{
		ReleaseMode:                   opts.ReleaseMode,
		AllowSkippedRegistrySemantics: opts.AllowSkippedRegistrySemantics,
	}
	if err := ValidateManifestAgainstRegistry(manifest, opts.Registry, regOpts); err != nil {
		return releaseFailCheck("registry_admission_passed",
			"Release manifest artifacts satisfy ArtifactRegistry.v0",
			"PCS_REGISTRY_ADMISSION_FAILED",
			map[string]any{"error": err.Error()}), []string{"PCS_REGISTRY_ADMISSION_FAILED"}
	}
	return releasePassCheck("registry_admission_passed",
		"Release manifest artifacts satisfy ArtifactRegistry.v0",
		map[string]any{"registry_id": opts.Registry.RegistryID}), nil
}

func loadReleaseChainCertificateID(baseDir string) (string, error) {
	certPath := filepath.Join(baseDir, "science_claim_bundle.certified.json")
	if !fileExists(certPath) {
		return "", fmt.Errorf("science_claim_bundle.certified.json not found")
	}
	bundle, err := LoadScienceClaimBundle(certPath)
	if err != nil {
		return "", err
	}
	cert := firstCertificate(bundle)
	if cert == nil {
		return "", fmt.Errorf("no certificate in certified bundle")
	}
	return cert.CertificateID, nil
}

func loadReleaseChainTraceHash(baseDir string) (string, error) {
	certPath := filepath.Join(baseDir, "science_claim_bundle.certified.json")
	bundle, err := LoadScienceClaimBundle(certPath)
	if err != nil {
		return "", err
	}
	r := bundle.PrimaryRuntimeReceipt()
	if r == nil || strings.TrimSpace(r.TraceHash) == "" {
		return "", fmt.Errorf("runtime receipt trace_hash missing")
	}
	return r.TraceHash, nil
}

func loadVerificationResultFile(path string) (VerificationResult, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return VerificationResult{}, err
	}
	var vr VerificationResult
	if err := json.Unmarshal(data, &vr); err != nil {
		return VerificationResult{}, err
	}
	return vr, nil
}

func fileExists(path string) bool {
	st, err := os.Stat(path)
	return err == nil && !st.IsDir()
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
		checks = normalizeReleaseChainChecks(map[string]ReleaseValidationCheck{
			"manifest_hashes_match": releaseFailCheck("manifest_hashes_match",
				"Release manifest matches pcs-core JSON Schema",
				"PCS_SCHEMA_INVALID", map[string]any{"error": schemaErr.Error()}),
		})
		failureCodes = []string{"PCS_SCHEMA_INVALID"}
	}
	if len(checks) == 0 {
		checks = normalizeReleaseChainChecks(nil)
	}
	status := StatusProofChecked
	for _, c := range checks {
		if c.Status == "failed" {
			status = StatusRejected
		}
	}
	if len(failureCodes) > 0 {
		status = StatusRejected
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
	checks = finalizeReleaseChainChecks(checks, opts.AdmissionProfile)
	status = StatusProofChecked
	for _, c := range checks {
		if c.Status == "failed" {
			status = StatusRejected
		}
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
	if err := ValidateRegistrySemanticCheckRecords(result.Checks); err != nil {
		return result, fmt.Errorf("release chain validation result semantics: %w", err)
	}
	return result, nil
}

// BuildReleaseChainValidationResultFromVerification maps bundle verification into RCVR for PF admission.
func BuildReleaseChainValidationResultFromVerification(
	manifest *ReleaseManifest,
	manifestPath string,
	bundleResult VerificationResult,
	handoff *HandoffManifest,
	registry *ArtifactRegistry,
	opts ReleaseChainVerifyOptions,
) (ReleaseChainValidationResult, error) {
	opts.Registry = registry
	artifactDir := opts.ArtifactDir
	if strings.TrimSpace(artifactDir) == "" && strings.TrimSpace(manifestPath) != "" {
		if resolved, err := ResolveArtifactPath(manifestPath); err == nil {
			artifactDir = filepath.Dir(resolved)
		}
	}
	opts.ArtifactDir = artifactDir

	var checks []ReleaseValidationCheck
	var failureCodes []string
	if manifest != nil {
		checks, failureCodes = runReleaseChainChecks(artifactDir, manifest, opts)
	}
	checks, failureCodes = appendVerificationAdmissionChecks(checks, failureCodes, handoff, bundleResult, opts)
	return buildReleaseChainResult(manifest, checks, failureCodes, opts, nil)
}

func releaseSkipCheck(id, description string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return ReleaseValidationCheck{
		CheckID: id, Description: description, Status: "skipped", Details: details,
		RegistryCheckRefs: []string{},
	}
}

func releasePassCheck(id, description string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	return ReleaseValidationCheck{
		CheckID: id, Description: description, Status: "passed", Details: details,
		RegistryCheckRefs: registryCheckRefsFor(id),
	}
}

func releaseFailCheck(id, description, failureCode string, details map[string]any) ReleaseValidationCheck {
	if details == nil {
		details = map[string]any{}
	}
	details["failure_code"] = failureCode
	return ReleaseValidationCheck{
		CheckID: id, Description: description, Status: "failed", Details: details,
		RegistryCheckRefs: registryCheckRefsFor(id),
	}
}

func registryCheckRefsFor(checkID string) []string {
	if checkID == "registry_admission_passed" {
		return append([]string(nil), RegistryReleaseChainCheckIDs...)
	}
	return []string{}
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

// DefaultReleaseManifestPath returns a colocated or pcs-core example release manifest when present.
func DefaultReleaseManifestPath(nearDir string) (string, bool) {
	if nearDir != "" {
		for _, name := range []string{"release_manifest.v0.json", "release_manifest.json"} {
			candidate := filepath.Join(nearDir, name)
			if fileExists(candidate) {
				return candidate, true
			}
		}
	}
	for _, base := range pcsCoreSearchRoots() {
		for _, name := range []string{
			filepath.Join("examples", "labtrust-release", "release_manifest.v0.json"),
			filepath.Join("examples", "release_manifest.valid.json"),
		} {
			candidate := filepath.Join(base, name)
			if fileExists(candidate) {
				return candidate, true
			}
		}
	}
	return "", false
}
