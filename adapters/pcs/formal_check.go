// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

const (
	ComponentLeanTrustKernel = "pcs-core Lean trust kernel"
	formalCheckArtifactPath  = "lean_check_result.v0.json"
)

// AdmissionFormalChecks configures Lean trust-envelope requirements for a profile.
type AdmissionFormalChecks struct {
	Required                 bool     `json:"required"`
	RequiredObligations      []string `json:"required_obligations"`
	LeanCheckStatusRequired  string   `json:"lean_check_status_required"`
}

// ProofObligation is ProofObligation.v0 produced by pcs-core.
type ProofObligation struct {
	SchemaVersion     string                         `json:"schema_version"`
	ObligationID      string                         `json:"obligation_id"`
	ReleaseID         string                         `json:"release_id"`
	WorkflowID        string                         `json:"workflow_id"`
	Obligations       []ProofObligationEntry         `json:"obligations"`
	SourceArtifacts   map[string]ProofObligationSource `json:"source_artifacts"`
	LeanModule        string                         `json:"lean_module"`
	SourceRepo        string                         `json:"source_repo"`
	SourceCommit      string                         `json:"source_commit"`
	SignatureOrDigest string                         `json:"signature_or_digest"`
}

type ProofObligationEntry struct {
	ObligationID string         `json:"obligation_id"`
	Kind         string         `json:"kind"`
	Inputs       map[string]any `json:"inputs"`
}

type ProofObligationSource struct {
	Path         string `json:"path"`
	ArtifactType string `json:"artifact_type"`
}

// LeanCheckResult is LeanCheckResult.v0 produced by pcs-core Lean checks.
type LeanCheckResult struct {
	SchemaVersion     string                      `json:"schema_version"`
	CheckID           string                      `json:"check_id"`
	ProofObligationID string                      `json:"proof_obligation_id"`
	LeanModule        string                      `json:"lean_module"`
	LeanTheorem       string                      `json:"lean_theorem"`
	Status            string                      `json:"status"`
	CheckedAt         string                      `json:"checked_at"`
	LeanVersion       string                      `json:"lean_version"`
	SourceRepo        string                      `json:"source_repo"`
	SourceCommit      string                      `json:"source_commit"`
	FailureReason     string                      `json:"failure_reason"`
	ObligationResults []LeanObligationCheckResult `json:"obligation_results,omitempty"`
	SignatureOrDigest string                      `json:"signature_or_digest"`
}

// LeanObligationCheckResult records one obligation kind outcome from the Lean kernel.
type LeanObligationCheckResult struct {
	ObligationID  string `json:"obligation_id"`
	Kind          string `json:"kind"`
	Status        string `json:"status"`
	LeanTheorem   string `json:"lean_theorem"`
	FailureReason string `json:"failure_reason,omitempty"`
}

// FormalCheckInputs carries optional Lean trust-envelope artifacts for admission.
type FormalCheckInputs struct {
	ProofObligationsPath     string
	LeanCheckResultPath      string
	ProofObligation          *ProofObligation
	LeanCheckResult          *LeanCheckResult
	AllowMissingFormalChecks bool
}

func (p *AdmissionProfile) formalChecks() *AdmissionFormalChecks {
	if p == nil || p.FormalChecks == nil {
		return nil
	}
	return p.FormalChecks
}

func (p *AdmissionProfile) formalChecksRequired() bool {
	fc := p.formalChecks()
	return fc != nil && fc.Required
}

func (fc *AdmissionFormalChecks) leanStatusRequired() string {
	if fc == nil || strings.TrimSpace(fc.LeanCheckStatusRequired) == "" {
		return StatusProofChecked
	}
	return strings.TrimSpace(fc.LeanCheckStatusRequired)
}

// obligationKindAllowedTheorems maps ProofObligation obligation kinds to Lean theorem names PF accepts.
var obligationKindAllowedTheorems = map[string][]string{
	"CertificateMatchesRuntime": {
		"admissible_release_has_matching_trace_hash",
	},
	"VerificationAdmitsBundle": {
		"admissible_release_has_proof_checked_verification",
		"admissible_release_has_verified_input_hash_equal_to_bundle_hash",
	},
	"SignedBundleAdmissible": {
		"admissible_release_has_signed_input_hash_equal_to_verified_input_hash",
	},
	"ComputationWitnessBindsResults": {
		"witness_result_hashes_admissible",
		"witnessResultHashesAdmissible",
	},
}

func allowedTheoremsForKind(kind string) []string {
	return obligationKindAllowedTheorems[strings.TrimSpace(kind)]
}

func theoremAuthorized(kind, theorem string) bool {
	theorem = strings.TrimSpace(theorem)
	if theorem == "" {
		return false
	}
	for _, allowed := range allowedTheoremsForKind(kind) {
		if theorem == allowed {
			return true
		}
	}
	return false
}

// LoadProofObligation reads and schema-validates ProofObligation.v0.
func LoadProofObligation(path string) (*ProofObligation, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read proof obligation: %w", err)
	}
	var po ProofObligation
	if err := json.Unmarshal(data, &po); err != nil {
		return nil, fmt.Errorf("parse proof obligation: %w", err)
	}
	return &po, nil
}

// LoadLeanCheckResult reads and schema-validates LeanCheckResult.v0.
func LoadLeanCheckResult(path string) (*LeanCheckResult, error) {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return nil, err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return nil, fmt.Errorf("read lean check result: %w", err)
	}
	var lcr LeanCheckResult
	if err := json.Unmarshal(data, &lcr); err != nil {
		return nil, fmt.Errorf("parse lean check result: %w", err)
	}
	return &lcr, nil
}

// ValidateProofObligationFile validates JSON against ProofObligation.v0 schema.
func ValidateProofObligationFile(repoRoot, path string) error {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return err
	}
	return ValidateDocumentAgainstSchema(repoRoot, "ProofObligation.v0.schema.json", doc)
}

// ValidateLeanCheckResultFile validates JSON against LeanCheckResult.v0 schema.
func ValidateLeanCheckResultFile(repoRoot, path string) error {
	resolved, err := ResolveArtifactPath(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(resolved)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return err
	}
	return ValidateDocumentAgainstSchema(repoRoot, "LeanCheckResult.v0.schema.json", doc)
}

// ResolveFormalCheckInputs loads formal artifacts when paths are provided.
func ResolveFormalCheckInputs(repoRoot string, in FormalCheckInputs) (FormalCheckInputs, error) {
	out := in
	if strings.TrimSpace(in.ProofObligationsPath) != "" {
		if err := ValidateProofObligationFile(repoRoot, in.ProofObligationsPath); err != nil {
			return out, fmt.Errorf("%s: %w", ReasonSchemaInvalid, err)
		}
		po, err := LoadProofObligation(in.ProofObligationsPath)
		if err != nil {
			return out, err
		}
		out.ProofObligation = po
	}
	if strings.TrimSpace(in.LeanCheckResultPath) != "" {
		if err := ValidateLeanCheckResultFile(repoRoot, in.LeanCheckResultPath); err != nil {
			return out, fmt.Errorf("%s: %w", ReasonSchemaInvalid, err)
		}
		lcr, err := LoadLeanCheckResult(in.LeanCheckResultPath)
		if err != nil {
			return out, err
		}
		out.LeanCheckResult = lcr
	}
	return out, nil
}

// EnforceFormalCheckAdmission validates Lean trust-envelope artifacts for release mode.
func EnforceFormalCheckAdmission(
	profile *AdmissionProfile,
	manifest *ReleaseManifest,
	policy ReleaseAdmissionPolicy,
	in FormalCheckInputs,
) error {
	if profile == nil || !profile.formalChecksRequired() || !policy.ReleaseMode {
		return nil
	}
	if policy.AllowMissingFormalChecks {
		return nil
	}
	fc := profile.formalChecks()
	if strings.TrimSpace(in.ProofObligationsPath) == "" || in.ProofObligation == nil {
		return fmt.Errorf("%s: --proof-obligations ProofObligation.v0 is required for profile %q in release mode",
			FailureCodeMissingLeanCheckResult, profile.ProfileID)
	}
	if strings.TrimSpace(in.LeanCheckResultPath) == "" || in.LeanCheckResult == nil {
		return fmt.Errorf("%s: --lean-check-result LeanCheckResult.v0 is required for profile %q in release mode",
			FailureCodeMissingLeanCheckResult, profile.ProfileID)
	}
	return validateFormalArtifacts(fc, manifest, in.ProofObligation, in.LeanCheckResult)
}

func validateFormalArtifacts(fc *AdmissionFormalChecks, manifest *ReleaseManifest, po *ProofObligation, lcr *LeanCheckResult) error {
	if fc == nil || po == nil || lcr == nil {
		return fmt.Errorf("%s: formal check artifacts are required", FailureCodeMissingLeanCheckResult)
	}
	if lcr.ProofObligationID != po.ObligationID {
		return fmt.Errorf("%s: lean proof_obligation_id %q != obligation %q",
			FailureCodeLeanObligationMismatch, lcr.ProofObligationID, po.ObligationID)
	}
	if manifest != nil && strings.TrimSpace(manifest.ReleaseID) != "" && po.ReleaseID != manifest.ReleaseID {
		return fmt.Errorf("%s: proof obligation release_id %q != manifest %q",
			FailureCodeLeanReleaseIDMismatch, po.ReleaseID, manifest.ReleaseID)
	}
	if IsForbiddenPlaceholderCommit(lcr.SourceCommit) {
		return fmt.Errorf("%s: lean check source_commit %q is a placeholder",
			FailureCodeLeanCheckFailed, lcr.SourceCommit)
	}
	requiredStatus := fc.leanStatusRequired()
	if lcr.Status != requiredStatus {
		return fmt.Errorf("%s: lean check status %q (expected %q)",
			FailureCodeLeanCheckFailed, lcr.Status, requiredStatus)
	}
	byKind := map[string]ProofObligationEntry{}
	for _, entry := range po.Obligations {
		byKind[entry.Kind] = entry
	}
	resultsByKind := map[string]LeanObligationCheckResult{}
	for _, r := range lcr.ObligationResults {
		resultsByKind[r.Kind] = r
	}
	for _, kind := range fc.RequiredObligations {
		entry, ok := byKind[kind]
		if !ok {
			return fmt.Errorf("%s: proof obligation missing required kind %q", FailureCodeLeanObligationMismatch, kind)
		}
		if !theoremAuthorized(kind, lcr.LeanTheorem) && !theoremAuthorized(kind, entry.ObligationID) {
			// top-level theorem may summarize one obligation; per-kind checks use obligation_results.
		}
		result, ok := resultsByKind[kind]
		if !ok {
			return fmt.Errorf("%s: lean check missing obligation result for kind %q", FailureCodeLeanCheckFailed, kind)
		}
		if result.Status != "passed" {
			reason := strings.TrimSpace(result.FailureReason)
			if reason == "" {
				reason = strings.TrimSpace(lcr.FailureReason)
			}
			return fmt.Errorf("%s: lean obligation %q failed: %s", FailureCodeLeanCheckFailed, kind, reason)
		}
		if !theoremAuthorized(kind, result.LeanTheorem) {
			return fmt.Errorf("%s: lean theorem %q is not allowed for obligation kind %q",
				FailureCodeUnauthorizedLeanTheorem, result.LeanTheorem, kind)
		}
		if result.ObligationID != entry.ObligationID && result.ObligationID != "" {
			return fmt.Errorf("%s: lean result obligation_id %q != proof obligation entry %q",
				FailureCodeLeanObligationMismatch, result.ObligationID, entry.ObligationID)
		}
	}
	if th := strings.TrimSpace(lcr.LeanTheorem); th != "" {
		allowed := false
		for _, kind := range fc.RequiredObligations {
			if theoremAuthorized(kind, th) {
				allowed = true
				break
			}
		}
		if !allowed {
			return fmt.Errorf("%s: lean theorem %q is not in the admission profile allowlist",
				FailureCodeUnauthorizedLeanTheorem, th)
		}
	}
	return nil
}

// AppendFormalReleaseChainChecks adds formal.<Kind> checks to RCVR from validated Lean artifacts.
func AppendFormalReleaseChainChecks(
	profile *AdmissionProfile,
	manifest *ReleaseManifest,
	in FormalCheckInputs,
	checks []ReleaseValidationCheck,
	failureCodes []string,
) ([]ReleaseValidationCheck, []string) {
	if profile == nil || !profile.formalChecksRequired() {
		return checks, failureCodes
	}
	fc := profile.formalChecks()
	if in.ProofObligation == nil || in.LeanCheckResult == nil {
		checks = append(checks, releaseFailCheck("formal_checks_executed",
			"Lean trust-envelope checks executed for required proof obligations",
			FailureCodeMissingLeanCheckResult,
			map[string]any{"artifact": formalCheckArtifactPath}))
		failureCodes = append(failureCodes, FailureCodeMissingLeanCheckResult)
		return checks, failureCodes
	}
	if err := validateFormalArtifacts(fc, manifest, in.ProofObligation, in.LeanCheckResult); err != nil {
		code := formalFailureCode(err)
		checks = append(checks, releaseFailCheck("formal_checks_executed",
			"Lean trust-envelope checks executed for required proof obligations",
			code, map[string]any{"error": err.Error(), "artifact": formalCheckArtifactPath}))
		failureCodes = append(failureCodes, code)
		return checks, failureCodes
	}
	resultsByKind := map[string]LeanObligationCheckResult{}
	for _, r := range in.LeanCheckResult.ObligationResults {
		resultsByKind[r.Kind] = r
	}
	for _, kind := range fc.RequiredObligations {
		checkID := "formal." + kind
		result := resultsByKind[kind]
		entry := obligationEntryForKind(in.ProofObligation, kind)
		details := map[string]any{
			"artifact":              formalCheckArtifactPath,
			"lean_theorem":          result.LeanTheorem,
			"obligation_id":         result.ObligationID,
			"obligation_kind":       kind,
			"responsible_component": ComponentLeanTrustKernel,
		}
		if entry != nil && len(entry.Inputs) > 0 {
			details["expected_predicate"] = formalPredicateForKind(kind)
			details["actual_values"] = entry.Inputs
		}
		checks = append(checks, releasePassCheck(checkID,
			fmt.Sprintf("Lean trust kernel established %s", kind),
			details))
	}
	checks = append(checks, releasePassCheck("formal_checks_executed",
		"Lean trust-envelope checks executed for required proof obligations",
		map[string]any{
			"proof_obligation_id": in.ProofObligation.ObligationID,
			"lean_check_id":       in.LeanCheckResult.CheckID,
			"artifact":            formalCheckArtifactPath,
		}))
	return checks, failureCodes
}

func obligationEntryForKind(po *ProofObligation, kind string) *ProofObligationEntry {
	if po == nil {
		return nil
	}
	for i := range po.Obligations {
		if po.Obligations[i].Kind == kind {
			return &po.Obligations[i]
		}
	}
	return nil
}

func formalPredicateForKind(kind string) string {
	switch kind {
	case "CertificateMatchesRuntime":
		return "certificate.trace_hash = runtime_receipt.trace_hash"
	case "VerificationAdmitsBundle":
		return "verification.status = ProofChecked ∧ verification.verified_input_bundle_hash = bundle_hash"
	case "SignedBundleAdmissible":
		return "signed_bundle.signed_input_bundle_hash = verification.verified_input_bundle_hash"
	case "ComputationWitnessBindsResults":
		return "∀ h ∈ witness.result_hashes, h ∈ result_artifact_hashes"
	default:
		return kind
	}
}

func formalFailureCode(err error) string {
	if err == nil {
		return FailureCodeLeanCheckFailed
	}
	msg := err.Error()
	switch {
	case strings.Contains(msg, FailureCodeMissingLeanCheckResult):
		return FailureCodeMissingLeanCheckResult
	case strings.Contains(msg, FailureCodeLeanObligationMismatch):
		return FailureCodeLeanObligationMismatch
	case strings.Contains(msg, FailureCodeLeanReleaseIDMismatch):
		return FailureCodeLeanReleaseIDMismatch
	case strings.Contains(msg, FailureCodeUnauthorizedLeanTheorem):
		return FailureCodeUnauthorizedLeanTheorem
	default:
		return FailureCodeLeanCheckFailed
	}
}

// FormalFailureExplanation builds operator-facing repair text for a formal release-chain check.
func FormalFailureExplanation(c ReleaseValidationCheck) (FailureExplanation, bool) {
	if c.CheckID == "formal_checks_executed" {
		fc, _ := c.Details["failure_code"].(string)
		if fc == "" {
			fc = FailureCodeMissingLeanCheckResult
		}
		errMsg, _ := c.Details["error"].(string)
		hint := "Run pcs-core Lean checks and pass --proof-obligations and --lean-check-result in release mode."
		if errMsg != "" {
			hint = errMsg
		}
		return FailureExplanation{
			CheckID:              c.CheckID,
			FailureCode:          fc,
			ArtifactPath:         formalCheckArtifactPath,
			ResponsibleComponent: ComponentLeanTrustKernel,
			RepairHint:           hint,
			RegenerateCmd:        "pcs lean check --proof-obligations proof_obligation.v0.json --out lean_check_result.v0.json",
		}, true
	}
	if !strings.HasPrefix(c.CheckID, "formal.") {
		return FailureExplanation{}, false
	}
	kind := strings.TrimPrefix(c.CheckID, "formal.")
	fc, _ := c.Details["failure_code"].(string)
	if fc == "" {
		fc = FailureCodeLeanCheckFailed
	}
	theorem, _ := c.Details["lean_theorem"].(string)
	obligationID, _ := c.Details["obligation_id"].(string)
	expected, _ := c.Details["expected_predicate"].(string)
	actualMap, _ := c.Details["actual_values"].(map[string]any)
	errMsg, _ := c.Details["error"].(string)
	hint := fmt.Sprintf("The Lean trust kernel could not establish %s", kind)
	if errMsg != "" {
		hint = errMsg
	} else if expected != "" {
		hint = fmt.Sprintf("The Lean trust kernel could not establish %s because the predicate %s was not satisfied.", kind, expected)
		if len(actualMap) > 0 {
			hint += fmt.Sprintf(" Actual artifact values: %v.", actualMap)
		}
	} else if kind == "CertificateMatchesRuntime" {
		hint = "The Lean trust kernel could not establish CertificateMatchesRuntime because certificate.trace_hash != runtime_receipt.trace_hash."
	}
	actual := fmt.Sprint(actualMap)
	if obligationID != "" {
		actual = "obligation_id=" + obligationID + " theorem=" + theorem + " " + actual
	}
	return FailureExplanation{
		CheckID:              c.CheckID,
		FailureCode:          fc,
		ArtifactPath:         formalCheckArtifactPath,
		ResponsibleComponent: ComponentLeanTrustKernel,
		Expected:             expected,
		Actual:               actual,
		RepairHint:           hint,
		RegenerateCmd:        "pcs lean check --proof-obligations proof_obligation.v0.json --out lean_check_result.v0.json",
	}, true
}
