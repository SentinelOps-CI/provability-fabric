// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"strings"
	"time"
)

// PCSBenchmarkCommandEntry matches common.defs.json#benchmark_command_entry.
type PCSBenchmarkCommandEntry struct {
	Command      string `json:"command"`
	ExitCode     int    `json:"exit_code"`
	StdoutDigest string `json:"stdout_digest,omitempty"`
}

// PCSBenchmarkRun matches pcs-core BenchmarkRun.v0 (per case).
type PCSBenchmarkRun struct {
	SchemaVersion                string                   `json:"schema_version"`
	RunID                        string                   `json:"run_id"`
	TaskID                       string                   `json:"task_id"`
	CaseID                       string                   `json:"case_id"`
	StartedAt                    string                   `json:"started_at"`
	CompletedAt                  string                   `json:"completed_at"`
	Commands                     []PCSBenchmarkCommandEntry `json:"commands"`
	ArtifactsProduced            []string                 `json:"artifacts_produced"`
	ObservedStatus               string                   `json:"observed_status"`
	ObservedFailureCode          *string                  `json:"observed_failure_code"`
	ObservedResponsibleComponent *string                  `json:"observed_responsible_component"`
	ObservedRepairHint           *string                  `json:"observed_repair_hint"`
	DurationMS                   int                      `json:"duration_ms"`
	SourceRepo                   string                   `json:"source_repo"`
	SourceCommit                 string                   `json:"source_commit"`
	SignatureOrDigest            string                   `json:"signature_or_digest"`
}

// PCSFailureLocalizationResult matches pcs-core FailureLocalizationResult.v0.
type PCSFailureLocalizationResult struct {
	SchemaVersion                 string `json:"schema_version"`
	ResultID                      string `json:"result_id"`
	RunID                         string `json:"run_id"`
	CaseID                        string `json:"case_id"`
	ExpectedFailureCode           string `json:"expected_failure_code"`
	ObservedFailureCode           string `json:"observed_failure_code"`
	ExpectedResponsibleComponent  string `json:"expected_responsible_component"`
	ObservedResponsibleComponent  string `json:"observed_responsible_component"`
	LocalizedCorrectly            bool   `json:"localized_correctly"`
	SourceRepo                    string `json:"source_repo"`
	SourceCommit                  string `json:"source_commit"`
	SignatureOrDigest             string `json:"signature_or_digest"`
}

// PCSCoverageReport matches pcs-core CoverageReport.v0 (single metric).
type PCSCoverageReport struct {
	SchemaVersion     string         `json:"schema_version"`
	CoverageID        string         `json:"coverage_id"`
	Metric            string         `json:"metric"`
	MetricID          string         `json:"metric_id,omitempty"`
	Numerator         float64        `json:"numerator"`
	Denominator       float64        `json:"denominator"`
	CoverageRatio     float64        `json:"coverage_ratio"`
	Details           map[string]any `json:"details"`
	SourceRepo        string         `json:"source_repo"`
	SourceCommit      string         `json:"source_commit"`
	SignatureOrDigest string         `json:"signature_or_digest"`
}

// PCSMetricSummary matches pcs-core MetricSummary.v0 (standalone artifact).
type PCSMetricSummary struct {
	SchemaVersion     string         `json:"schema_version"`
	MetricID          string         `json:"metric_id"`
	Score             float64        `json:"score"`
	Applicability     string         `json:"applicability"`
	Numerator         float64        `json:"numerator"`
	Denominator       float64        `json:"denominator"`
	Reason            string         `json:"reason"`
	Details           map[string]any `json:"details"`
	SourceRepo        string         `json:"source_repo"`
	SourceCommit      string         `json:"source_commit"`
	SignatureOrDigest string         `json:"signature_or_digest"`
}

// PCSBenchmarkReportMetricSummary is the BenchmarkReport.v0 metric_summaries[] row shape.
type PCSBenchmarkReportMetricSummary struct {
	Name          string   `json:"name"`
	Score         *float64 `json:"score,omitempty"`
	Applicability string   `json:"applicability"`
	Reason        string   `json:"reason,omitempty"`
	Numerator     int      `json:"numerator,omitempty"`
	Denominator   int      `json:"denominator,omitempty"`
}

// PCSBenchmarkReport matches pcs-core BenchmarkReport.v0.
type PCSBenchmarkReport struct {
	SchemaVersion     string                      `json:"schema_version"`
	ReportID          string                      `json:"report_id"`
	BenchmarkSuiteID  string                      `json:"benchmark_suite_id"`
	Runs              []PCSBenchmarkReportRunRef  `json:"runs"`
	Metrics           []string                    `json:"metrics"`
	MetricSummaries   []PCSBenchmarkReportMetricSummary `json:"metric_summaries"`
	Summary           PCSBenchmarkSummary         `json:"summary"`
	Coverage          PCSBenchmarkCoverageBlock   `json:"coverage"`
	Failures          []PCSBenchmarkFailureEntry  `json:"failures"`
	ProducerID        string                      `json:"producer_id,omitempty"`
	SourceRepo        string                      `json:"source_repo"`
	SourceCommit      string                      `json:"source_commit"`
	SignatureOrDigest string                      `json:"signature_or_digest"`
}

type PCSBenchmarkReportRunRef struct {
	RunID          string `json:"run_id"`
	CaseID         string `json:"case_id"`
	Path           string `json:"path"`
	ObservedStatus string `json:"observed_status,omitempty"`
}

type PCSBenchmarkSummary struct {
	TotalCases                        int     `json:"total_cases"`
	PassedCases                       int     `json:"passed_cases"`
	FailedCases                       int     `json:"failed_cases"`
	ExpectedFailuresDetected          int     `json:"expected_failures_detected"`
	UnexpectedPasses                  int     `json:"unexpected_passes"`
	UnexpectedFailures                int     `json:"unexpected_failures"`
	FailureLocalizationAccuracy       float64 `json:"failure_localization_accuracy"`
	RepairHintAccuracy                float64 `json:"repair_hint_accuracy"`
	FormalCheckCoverage               float64 `json:"formal_check_coverage"`
	RegistryCoverage                  float64 `json:"registry_coverage"`
	ScientificMemoryRenderCoverage    float64 `json:"scientific_memory_render_coverage"`
}

type PCSBenchmarkCoverageBlock struct {
	Registry               *PCSCoverageReport `json:"registry,omitempty"`
	FormalChecks           *PCSCoverageReport `json:"formal_checks,omitempty"`
	ScientificMemory       *PCSCoverageReport `json:"scientific_memory,omitempty"`
	ReleaseReproducibility *PCSCoverageReport `json:"release_reproducibility,omitempty"`
	CertificateCompleteness *PCSCoverageReport `json:"certificate_completeness,omitempty"`
}

type PCSBenchmarkFailureEntry struct {
	CaseID  string `json:"case_id"`
	RunID   string `json:"run_id,omitempty"`
	Message string `json:"message"`
}

// PCSExplainQualityReport matches pcs-core ExplainQualityReport.v0 (per case).
type PCSExplainQualityReport struct {
	SchemaVersion          string                            `json:"schema_version"`
	ReportID               string                            `json:"report_id"`
	SuiteID                string                            `json:"suite_id"`
	CaseID                 string                            `json:"case_id"`
	ProducerID             string                            `json:"producer_id"`
	WorkflowID             string                            `json:"workflow_id,omitempty"`
	RequiredSections       []string                          `json:"required_sections"`
	Sections               map[string]PCSExplainSectionScore `json:"sections"`
	SectionsPresentCount   int                               `json:"sections_present_count"`
	SectionsRequiredCount  int                               `json:"sections_required_count"`
	QualityScore           float64                           `json:"quality_score"`
	Gaps                   []PCSExplainQualityGap            `json:"gaps"`
	SourceRepo             string                            `json:"source_repo"`
	SourceCommit           string                            `json:"source_commit"`
	SignatureOrDigest      string                            `json:"signature_or_digest"`
}

type PCSExplainSectionScore struct {
	Present bool    `json:"present"`
	Score   float64 `json:"score"`
	Notes   string  `json:"notes,omitempty"`
}

type PCSExplainQualityGap struct {
	SectionID string `json:"section_id"`
	Message   string `json:"message"`
}

// PCSBenchmarkBundle is the on-disk layout consumable by pcs-bench.
type PCSBenchmarkBundle struct {
	Report              PCSBenchmarkReport
	Runs                []PCSBenchmarkRun
	FailureLocalizations []PCSFailureLocalizationResult
	ExplainQuality      []PCSExplainQualityReport
	CoverageByMetric    map[string]PCSCoverageReport
	Commands            []PCSBenchmarkCommandEntry
	Workflow            AdmissionBenchmarkWorkflow
	Profile             *AdmissionProfile
	CovReport           CoverageReportV0
	InternalSuite       AdmissionBenchmarkSuiteV0
}

type benchmarkCaseExecution struct {
	Case       AdmissionBenchmarkCase
	Result     AdmissionBenchmarkCaseResult
	RCVR       *ReleaseChainValidationResult
	VR         *VerificationResult
	Loc        *FailureLocalizationCaseResult
	Explain    *ExplainQualityCaseScore
	PCSExplain *PCSExplainQualityReport
	Started    time.Time
	Completed  time.Time
	Command    string
	ExitCode   int
	LogLines   []string
}

func suiteIDFromWorkflow(workflowID string) string {
	s := strings.ReplaceAll(workflowID, ".", "-")
	s = strings.ReplaceAll(s, "_", "-")
	return s
}

// pcsBenchmarkWorkflowID maps PF admission workflow folder ids to pcs-core registry workflow ids.
func pcsBenchmarkWorkflowID(admissionWorkflowID string) string {
	switch admissionWorkflowID {
	case "labtrust_qc_release":
		return "hospital_lab.qc_release"
	default:
		return admissionWorkflowID
	}
}

// pcsBenchmarkSuiteID is the pcs-bench producer suite id for PF admission benchmarks.
func pcsBenchmarkSuiteID(admissionWorkflowID string) string {
	switch admissionWorkflowID {
	case "labtrust_qc_release":
		return "pf-labtrust-admission-v0"
	case "agent_tool_use.safety_v0":
		return "pf-tool-use-admission-v0"
	case "scientific_computation.reproducibility_v0":
		return "pf-computation-admission-v0"
	case "formal_trust_kernel.enforcement_v0":
		return "pf-formal-admission-v0"
	default:
		w := pcsBenchmarkWorkflowID(admissionWorkflowID)
		return "pf-" + suiteIDFromWorkflow(w) + "-v0"
	}
}

func taskIDFromWorkflow(workflowID string) string {
	switch workflowID {
	case "labtrust_qc_release":
		return "labtrust-qc-release-v0"
	case "agent_tool_use.safety_v0":
		return "tool-use-safety-v0"
	case "scientific_computation.reproducibility_v0":
		return "computation-reproducibility-v0"
	case "formal_trust_kernel.enforcement_v0":
		return "formal-trust-kernel-v0"
	default:
		return suiteIDFromWorkflow(workflowID)
	}
}

func benchmarkObservedStatus(cr AdmissionBenchmarkCaseResult) string {
	if cr.Outcome == "error" {
		return "error"
	}
	if cr.Passed {
		return "passed"
	}
	return "failed"
}

func mapResponsibleComponent(component string) string {
	switch component {
	case ComponentProvabilityFabric:
		return "verifier"
	case ComponentLabTrustGym:
		return "certificate_producer"
	case "pcs-core":
		return "registry"
	case "scientific_memory", "ScientificMemory", "Scientific Memory":
		return "scientific_memory"
	default:
		if strings.Contains(strings.ToLower(component), "handoff") {
			return "handoff"
		}
		if strings.Contains(strings.ToLower(component), "formal") {
			return "formal_kernel"
		}
		return "unknown"
	}
}

func firstObservedFailureCode(codes []string) string {
	if len(codes) == 0 {
		return ""
	}
	return codes[0]
}

func buildPCSBenchmarkRun(
	ctx benchmarkCaseExecution,
	suiteID, taskID, sourceCommit string,
) PCSBenchmarkRun {
	cr := ctx.Result
	status := benchmarkObservedStatus(cr)
	var fcPtr, respPtr, repairPtr *string
	fcDigest := ""
	if status != "passed" {
		fc := firstObservedFailureCode(cr.ObservedFailureCodes)
		fcDigest = fc
		fcPtr = stringPtr(fc)
		resp := "unknown"
		repairHint := ""
		if ctx.RCVR != nil {
			for _, c := range ctx.RCVR.Checks {
				if c.Status == "failed" {
					resp = mapResponsibleComponent(c.ResponsibleComponent)
					if rh, ok := c.Details["repair_hint"].(string); ok && rh != "" {
						repairHint = rh
					}
					break
				}
			}
		}
		if ctx.VR != nil {
			for _, exp := range ExplainVerificationFailures(*ctx.VR) {
				if exp.RepairHint != "" {
					repairHint = exp.RepairHint
				}
				if exp.ResponsibleComponent != "" {
					resp = mapResponsibleComponent(exp.ResponsibleComponent)
				}
				break
			}
		}
		respPtr = stringPtr(resp)
		repairPtr = stringPtr(repairHint)
	}
	duration := int(ctx.Completed.Sub(ctx.Started).Milliseconds())
	if duration < 0 {
		duration = 0
	}
	runID := fmt.Sprintf("bench-run-%s", cr.CaseID)
	return PCSBenchmarkRun{
		SchemaVersion:                SchemaVersionV0,
		RunID:                        runID,
		TaskID:                       taskID,
		CaseID:                       cr.CaseID,
		StartedAt:                    ctx.Started.UTC().Format(time.RFC3339),
		CompletedAt:                  ctx.Completed.UTC().Format(time.RFC3339),
		Commands:                     []PCSBenchmarkCommandEntry{{Command: ctx.Command, ExitCode: ctx.ExitCode}},
		ArtifactsProduced:            artifactPathsForCase(ctx),
		ObservedStatus:               status,
		ObservedFailureCode:          fcPtr,
		ObservedResponsibleComponent: respPtr,
		ObservedRepairHint:           repairPtr,
		DurationMS:                   duration,
		SourceRepo:                   VerifierSourceRepo,
		SourceCommit:                 sourceCommit,
		SignatureOrDigest:            digestBenchmarkRun(runID, taskID, cr.CaseID, status, fcDigest),
	}
}

func stringPtr(s string) *string {
	if s == "" {
		return nil
	}
	return &s
}

func benchmarkRunFailureCode(run PCSBenchmarkRun) string {
	if run.ObservedFailureCode == nil {
		return ""
	}
	return *run.ObservedFailureCode
}

func artifactPathsForCase(ctx benchmarkCaseExecution) []string {
	out := []string{}
	if ctx.RCVR != nil {
		out = append(out, "release_chain_validation_result.v0.json")
	}
	if ctx.VR != nil {
		out = append(out, "verification_result.json")
	}
	return out
}

func digestBenchmarkRun(runID, taskID, caseID, status, failureCode string) string {
	sum := sha256.Sum256([]byte(strings.Join([]string{runID, taskID, caseID, status, failureCode}, "|")))
	return "sha256:" + hex.EncodeToString(sum[:])
}

func responsibleComponentForCheckID(checkID string) string {
	lower := strings.ToLower(checkID)
	switch {
	case strings.Contains(lower, "hash"), strings.Contains(lower, "digest"), strings.Contains(lower, "signed_input"),
		strings.Contains(lower, "bundle_hash"), strings.Contains(lower, "trace_hash"), strings.Contains(lower, "manifest_hash"),
		strings.Contains(lower, "result_hash"), strings.Contains(lower, "policy_hash"):
		return "hashing"
	case strings.HasPrefix(lower, "formal."), strings.Contains(lower, "lean"), strings.Contains(lower, "proof_obligation"):
		return "formal_kernel"
	case strings.Contains(lower, "handoff"), strings.Contains(lower, "bundle_to_verifier"):
		return "handoff"
	case strings.Contains(lower, "registry"), strings.Contains(lower, "artifact_registry"):
		return "registry"
	case strings.Contains(lower, "manifest"):
		return "release_manifest"
	case strings.Contains(lower, "certificate"), strings.Contains(lower, "trace_certificate"):
		return "certificate_producer"
	case strings.Contains(lower, "scientific_memory"):
		return "scientific_memory"
	default:
		if comp := benchmarkFailureCodeToComponent(checkID); comp != "" {
			return comp
		}
		return "verifier"
	}
}

func expectedResponsibleComponentForCase(c AdmissionBenchmarkCase) string {
	if c.Localization != nil && c.Localization.CheckID != "" {
		return responsibleComponentForCheckID(c.Localization.CheckID)
	}
	for _, code := range c.ExpectFailureCodes {
		if comp := benchmarkFailureCodeToComponent(code); comp != "" {
			return comp
		}
	}
	if expectsFormalFailure(c.ExpectFailureCodes) {
		return "formal_kernel"
	}
	return "verifier"
}

func failureLocalizationComponents(ctx benchmarkCaseExecution) (expected, observed string) {
	wantCheck := ""
	wantArtifact := ""
	if ctx.Case.Localization != nil {
		wantCheck = ctx.Case.Localization.CheckID
		wantArtifact = ctx.Case.Localization.ArtifactPath
	}
	expected = expectedResponsibleComponentForCase(ctx.Case)
	observed = "unknown"
	if ctx.RCVR != nil {
		for _, c := range ctx.RCVR.Checks {
			if c.Status != "failed" {
				continue
			}
			if wantCheck != "" && c.CheckID != wantCheck {
				continue
			}
			observed = responsibleComponentForCheckID(c.CheckID)
			if observed == "unknown" || observed == "verifier" {
				if mapped := mapResponsibleComponent(c.ResponsibleComponent); mapped != "unknown" {
					observed = mapped
				}
			}
			if wantCheck != "" {
				break
			}
		}
	}
	if observed == "unknown" && ctx.VR != nil {
		for _, exp := range ExplainVerificationFailures(*ctx.VR) {
			if exp.ResponsibleComponent != "" {
				observed = mapResponsibleComponent(exp.ResponsibleComponent)
				break
			}
		}
	}
	if observed == "unknown" && wantArtifact != "" {
		if strings.Contains(wantArtifact, "handoff") {
			observed = "handoff"
		} else if strings.Contains(wantArtifact, "registry") {
			observed = "registry"
		}
	}
	_ = wantArtifact
	return expected, observed
}

func buildPCSFailureLocalization(
	ctx benchmarkCaseExecution,
	taskID, sourceCommit string,
) *PCSFailureLocalizationResult {
	if ctx.Case.Kind != "invalid" || len(ctx.Case.ExpectFailureCodes) == 0 {
		return nil
	}
	cr := ctx.Result
	runID := fmt.Sprintf("bench-run-%s", cr.CaseID)
	resultID := fmt.Sprintf("flr-%s", cr.CaseID)
	expectedFC := firstObservedFailureCode(cr.ExpectFailureCodes)
	if ctx.Case.Localization != nil && ctx.Case.Localization.CheckID != "" {
		expectedFC = ctx.Case.Localization.CheckID
	}
	observedFC := firstObservedFailureCode(cr.ObservedFailureCodes)
	if ctx.RCVR != nil && ctx.Case.Localization != nil && ctx.Case.Localization.CheckID != "" {
		for _, chk := range ctx.RCVR.Checks {
			if chk.Status == "failed" && chk.CheckID == ctx.Case.Localization.CheckID {
				observedFC = chk.CheckID
				break
			}
		}
	}
	expectedResp, observedResp := failureLocalizationComponents(ctx)
	localized := cr.FailureCodeMatch && expectedResp == observedResp && observedResp != "unknown"
	if ctx.Loc != nil {
		localized = localized && ctx.Loc.Passed
	}
	return &PCSFailureLocalizationResult{
		SchemaVersion:                SchemaVersionV0,
		ResultID:                     resultID,
		RunID:                        runID,
		CaseID:                       cr.CaseID,
		ExpectedFailureCode:          expectedFC,
		ObservedFailureCode:          observedFC,
		ExpectedResponsibleComponent: expectedResp,
		ObservedResponsibleComponent: observedResp,
		LocalizedCorrectly:           localized,
		SourceRepo:                   VerifierSourceRepo,
		SourceCommit:                 sourceCommit,
		SignatureOrDigest:            digestBenchmarkRun(resultID, runID, cr.CaseID, "flr", observedFC),
	}
}

func explainAdmissionError(msg string, expectCodes []string) FailureExplanation {
	fe := FailureExplanation{
		Actual:               msg,
		RepairHint:           msg,
		ResponsibleComponent: ComponentProvabilityFabric,
		ArtifactPath:         formalCheckArtifactPath,
	}
	if len(expectCodes) > 0 {
		fe.Expected = strings.Join(expectCodes, ", ")
	}
	for _, code := range allAdmissionFailureCodes() {
		if strings.Contains(msg, code) {
			fe.FailureCode = code
			break
		}
	}
	if fe.FailureCode == "" && len(expectCodes) > 0 {
		fe.FailureCode = expectCodes[0]
	}
	if strings.Contains(msg, FailureCodeReleaseModeHandoffRequired) ||
		strings.Contains(msg, FailureCodeLegacyHandoffForbiddenInReleaseMode) {
		fe.ResponsibleComponent = ComponentProvabilityFabric
		fe.HandoffRef = "handoff_to_pf.json"
		fe.ArtifactPath = "handoff_to_pf.json"
	}
	if strings.Contains(strings.ToLower(msg), "theorem") || strings.Contains(msg, "admissible_") {
		fe.Expected = "authorized Lean theorem"
		fe.ResponsibleComponent = ComponentLeanTrustKernel
	}
	return fe
}

func enrichFailureExplanation(fe, fallback FailureExplanation) FailureExplanation {
	if fe.FailureCode == "" {
		fe.FailureCode = fallback.FailureCode
	}
	if fe.Expected == "" {
		fe.Expected = fallback.Expected
	}
	if fe.Actual == "" {
		fe.Actual = fallback.Actual
	}
	if fe.ResponsibleComponent == "" {
		fe.ResponsibleComponent = fallback.ResponsibleComponent
	}
	if fe.RepairHint == "" {
		fe.RepairHint = fallback.RepairHint
	}
	if fe.ArtifactPath == "" {
		fe.ArtifactPath = fallback.ArtifactPath
	}
	if fe.RegistryCheckRef == "" {
		fe.RegistryCheckRef = fallback.RegistryCheckRef
	}
	if fe.HandoffRef == "" {
		fe.HandoffRef = fallback.HandoffRef
	}
	return fe
}

func pickFailureExplanation(
	explanations []FailureExplanation,
	expectCodes []string,
	wantCheck string,
	fallback FailureExplanation,
) FailureExplanation {
	for _, fe := range explanations {
		if wantCheck != "" && fe.CheckID == wantCheck {
			return enrichFailureExplanation(fe, fallback)
		}
	}
	for _, code := range expectCodes {
		for _, fe := range explanations {
			if fe.FailureCode == code || strings.Contains(fe.Actual, code) || strings.Contains(fe.RepairHint, code) {
				return enrichFailureExplanation(fe, fallback)
			}
		}
	}
	if len(explanations) > 0 {
		return enrichFailureExplanation(explanations[0], fallback)
	}
	return fallback
}

// explainSectionIDForRequirement maps PF explain fields to pcs-core ExplainQualityReport section IDs.
func explainSectionIDForRequirement(field string) string {
	switch field {
	case "failure_code", "registry_check_ref", "expected", "actual":
		return "verification"
	case "artifact_path":
		return "provenance"
	case "responsible_component", "repair_hint":
		return "repair_hints"
	case "handoff_ref":
		return "handoffs"
	case "formal_theorem":
		return "formal_checks"
	default:
		return "verification"
	}
}

func buildPCSExplainQualityReport(
	c AdmissionBenchmarkCase,
	cr AdmissionBenchmarkCaseResult,
	rcvr *ReleaseChainValidationResult,
	vr *VerificationResult,
	sourceCommit, suiteID, workflowID string,
) *PCSExplainQualityReport {
	if c.ExplainRequirements == nil || c.Kind != "invalid" {
		return nil
	}
	req := c.ExplainRequirements
	required := append([]string(nil), CanonicalExplainQualitySections...)
	sections := map[string]PCSExplainSectionScore{}
	gaps := []PCSExplainQualityGap{}

	var explanations []FailureExplanation
	if rcvr != nil {
		report := BuildExplainReleaseChainReport(*rcvr)
		explanations = report.Failed
	} else if vr != nil {
		explanations = ExplainVerificationFailures(*vr)
	}
	fallback := explainAdmissionError(cr.Error, c.ExpectFailureCodes)
	if strings.TrimSpace(cr.Error) != "" && len(explanations) == 0 {
		explanations = []FailureExplanation{fallback}
	}
	wantCheck := ""
	if c.Localization != nil {
		wantCheck = c.Localization.CheckID
	}
	target := pickFailureExplanation(explanations, c.ExpectFailureCodes, wantCheck, fallback)

	combined := strings.ToLower(
		target.RepairHint + target.Actual + target.Expected + target.FailureCode +
			target.ArtifactPath + target.RegistryCheckRef + target.HandoffRef,
	)
	hashFailure := false
	for _, code := range c.ExpectFailureCodes {
		if strings.Contains(strings.ToLower(code), "hash") || strings.Contains(strings.ToLower(code), "mismatch") {
			hashFailure = true
			break
		}
	}
	hasHashEvidence := strings.Contains(combined, "sha256:") ||
		strings.Contains(combined, "hash") ||
		strings.Contains(combined, "digest")
	formalOK := strings.Contains(combined, "theorem") || strings.Contains(combined, "admissible_") ||
		strings.Contains(combined, "witness") || strings.Contains(combined, "lean") ||
		strings.Contains(combined, "proofobligation") || strings.Contains(combined, "leancheckresult")
	if !req.FormalTheorem && !expectsFormalFailure(c.ExpectFailureCodes) {
		formalOK = true
	}
	handoffOK := target.HandoffRef != "" || !req.HandoffRef
	limitationsNote := "admission profile bounds"
	if rcvr != nil {
		for _, chk := range rcvr.Checks {
			if chk.Status == "skipped" || chk.Status == "warning" {
				limitationsNote = fmt.Sprintf("deferred or skipped check %s", chk.CheckID)
				break
			}
		}
	}

	sectionSpecs := []struct {
		id      string
		present bool
		note    string
	}{
		{"provenance",
			target.ArtifactPath != "" || target.HandoffRef != "" || target.ResponsibleComponent != "" || target.RegistryCheckRef != "",
			target.ArtifactPath},
		{"hashes", hasHashEvidence || !hashFailure, combined},
		{"handoffs", handoffOK, target.HandoffRef},
		{"verification",
			target.FailureCode != "" ||
				target.Expected != "" ||
				target.Actual != "" ||
				target.RegistryCheckRef != "",
			target.FailureCode},
		{"formal_checks", formalOK, combined},
		{"limitations", true, limitationsNote},
		{"lineage", sourceCommit != "", sourceCommit},
		{"repair_hints", requirementEnabled(req, "repair_hint") && target.RepairHint != "", target.RepairHint},
	}
	for _, spec := range sectionSpecs {
		score := 0.0
		if spec.present {
			score = 1.0
		} else {
			gaps = append(gaps, PCSExplainQualityGap{
				SectionID: spec.id,
				Message:   fmt.Sprintf("missing evidence for explain section %s", spec.id),
			})
		}
		sections[spec.id] = PCSExplainSectionScore{
			Present: spec.present,
			Score:   score,
			Notes:   spec.note,
		}
	}
	requiredCount := len(required)
	var presentCount int
	for _, sectionID := range required {
		if sec, ok := sections[sectionID]; ok && sec.Present {
			presentCount++
		}
	}
	quality := 1.0
	if requiredCount > 0 {
		quality = float64(presentCount) / float64(requiredCount)
	}
	if quality > 1 {
		quality = 1
	}

	reportID := fmt.Sprintf("explain-quality-%s", c.CaseID)
	return &PCSExplainQualityReport{
		SchemaVersion:          SchemaVersionV0,
		ReportID:               reportID,
		SuiteID:                suiteID,
		CaseID:                 c.CaseID,
		ProducerID:             "provability-fabric",
		WorkflowID:             workflowID,
		RequiredSections:       required,
		Sections:               sections,
		SectionsPresentCount:   presentCount,
		SectionsRequiredCount:  requiredCount,
		QualityScore:           quality,
		Gaps:                   gaps,
		SourceRepo:             VerifierSourceRepo,
		SourceCommit:           sourceCommit,
		SignatureOrDigest:      digestBenchmarkRun(reportID, suiteID, c.CaseID, "explain", fmt.Sprintf("%f", quality)),
	}
}

func requirementEnabled(req *AdmissionBenchmarkExplainReq, field string) bool {
	switch field {
	case "failure_code":
		return req.FailureCode
	case "artifact_path":
		return req.ArtifactPath
	case "expected":
		return req.Expected
	case "actual":
		return req.Actual
	case "responsible_component":
		return req.ResponsibleComponent
	case "repair_hint":
		return req.RepairHint
	case "registry_check_ref":
		return req.RegistryCheckRef
	case "handoff_ref":
		return req.HandoffRef
	case "formal_theorem":
		return req.FormalTheorem
	default:
		return false
	}
}

func containsString(ss []string, want string) bool {
	for _, s := range ss {
		if s == want {
			return true
		}
	}
	return false
}

func newPCSCoverageReport(suiteID, sourceCommit, key, metricName, metricID string, ratio float64, details map[string]any) PCSCoverageReport {
	if details == nil {
		details = map[string]any{}
	}
	if ratio > 1 {
		ratio = 1
	}
	if ratio < 0 {
		ratio = 0
	}
	return PCSCoverageReport{
		SchemaVersion:     SchemaVersionV0,
		CoverageID:        suiteID + "-" + key,
		Metric:            metricName,
		MetricID:          metricID,
		Numerator:         ratio,
		Denominator:       1,
		CoverageRatio:     ratio,
		Details:           details,
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, metricID, ratio),
	}
}

func buildPCSCoverageReports(
	suiteID, sourceCommit string,
	metrics BenchmarkRunMetrics,
	cov AdmissionCoverageSnapshot,
) map[string]PCSCoverageReport {
	releaseRate := (metrics.ValidReleaseAdmissionRate + metrics.InvalidReleaseRejectionRate) / 2
	return map[string]PCSCoverageReport{
		"registry_coverage": newPCSCoverageReport(
			suiteID, sourceCommit, "registry", "registry_coverage", "registry_coverage_score",
			metrics.RegistryCheckCoverage,
			map[string]any{
				"registered_artifacts_checked": cov.RegisteredArtifactsChecked,
				"semantic_checks_executed":     cov.SemanticChecksExecuted,
				"semantic_checks_deferred":     cov.SemanticChecksDeferred,
				"semantic_checks_skipped":      cov.SemanticChecksSkipped,
			},
		),
		"formal_check_coverage": newPCSCoverageReport(
			suiteID, sourceCommit, "formal", "formal_check_coverage", "formal_check_coverage_score",
			metrics.FormalCheckEnforcementCoverage,
			map[string]any{"formal_checks_required": cov.FormalChecksRequired},
		),
		"release_reproducibility": newPCSCoverageReport(
			suiteID, sourceCommit, "release", "release_reproducibility", "release_reproducibility_score",
			releaseRate, map[string]any{},
		),
		"failure_localization": newPCSCoverageReport(
			suiteID, sourceCommit, "floc", "failure_localization", "failure_localization_accuracy",
			metrics.FailureLocalizationAccuracy, map[string]any{},
		),
		"certificate_completeness": newPCSCoverageReport(
			suiteID, sourceCommit, "cert", "certificate_completeness", "certificate_completeness_score",
			metrics.FailureCodeAccuracy, map[string]any{},
		),
		"admission_profile_coverage": newPCSCoverageReport(
			suiteID, sourceCommit, "profile", "cross_domain_portability", "cross_domain_portability_score",
			metrics.AdmissionProfileCoverage, map[string]any{"profile_id": "admission_profile"},
		),
	}
}

func digestCoverage(suiteID, metric string, ratio float64) string {
	sum := sha256.Sum256([]byte(fmt.Sprintf("%s|%s|%f", suiteID, metric, ratio)))
	return "sha256:" + hex.EncodeToString(sum[:])
}

// AdmissionCoverageSnapshot carries registry counters for coverage details.
type AdmissionCoverageSnapshot struct {
	RegisteredArtifactsChecked int
	SemanticChecksExecuted     int
	SemanticChecksDeferred     int
	SemanticChecksSkipped      int
	FormalChecksRequired       bool
}

func buildBenchmarkCoverageBlock(coverage map[string]PCSCoverageReport, reg, formal, rel PCSCoverageReport) PCSBenchmarkCoverageBlock {
	block := PCSBenchmarkCoverageBlock{
		Registry:               &reg,
		FormalChecks:           &formal,
		ReleaseReproducibility: &rel,
	}
	if cert, ok := coverage["certificate_completeness"]; ok {
		certCopy := cert
		block.CertificateCompleteness = &certCopy
	}
	return block
}

func clampUnitScore(score float64) float64 {
	if score > 1 {
		return 1
	}
	if score < 0 {
		return 0
	}
	return score
}

func buildPCSBenchmarkReportMetricSummaries(metrics BenchmarkRunMetrics) []PCSBenchmarkReportMetricSummary {
	releaseScore := clampUnitScore((metrics.ValidReleaseAdmissionRate + metrics.InvalidReleaseRejectionRate) / 2)
	repairHint := clampUnitScore(metrics.ExplainOutputCompleteness)
	specs := []struct {
		name  string
		score float64
	}{
		{"release_reproducibility_score", releaseScore},
		{"failure_localization_accuracy", clampUnitScore(metrics.FailureLocalizationAccuracy)},
		{"certificate_completeness_score", clampUnitScore(metrics.FailureCodeAccuracy)},
		{"registry_coverage_score", clampUnitScore(metrics.RegistryCheckCoverage)},
		{"formal_check_coverage_score", clampUnitScore(metrics.FormalCheckEnforcementCoverage)},
		{"scientific_memory_interpretability_score", 1.0},
		{"repair_hint_quality_score", repairHint},
		{"cross_domain_portability_score", clampUnitScore(metrics.AdmissionProfileCoverage)},
	}
	out := make([]PCSBenchmarkReportMetricSummary, 0, len(specs))
	for _, spec := range specs {
		score := spec.score
		scoreCopy := score
		num := int(score + 0.5)
		if num < 0 {
			num = 0
		}
		out = append(out, PCSBenchmarkReportMetricSummary{
			Name:          spec.name,
			Score:         &scoreCopy,
			Applicability: "measured",
			Reason:        "pf benchmark admission",
			Numerator:     num,
			Denominator:   1,
		})
	}
	return out
}

func buildPCSBenchmarkReport(
	suiteID, reportID, sourceCommit string,
	executions []benchmarkCaseExecution,
	metrics BenchmarkRunMetrics,
	coverage map[string]PCSCoverageReport,
) PCSBenchmarkReport {
	var runRefs []PCSBenchmarkReportRunRef
	failures := []PCSBenchmarkFailureEntry{}
	var total, passed, failed, expectedDetected, unexpectedPass, unexpectedFail int
	repairHintAccuracy := metrics.ExplainOutputCompleteness
	if repairHintAccuracy > 1 {
		repairHintAccuracy = 1
	}
	for _, ex := range executions {
		cr := ex.Result
		total++
		if cr.Passed {
			passed++
		} else {
			failed++
			failures = append(failures, PCSBenchmarkFailureEntry{
				CaseID:  cr.CaseID,
				RunID:   fmt.Sprintf("bench-run-%s", cr.CaseID),
				Message: strings.TrimSpace(cr.Error),
			})
			if failures[len(failures)-1].Message == "" {
				failures[len(failures)-1].Message = fmt.Sprintf("expected %s got %s", cr.Expect, cr.Outcome)
			}
		}
		if cr.Kind == "invalid" {
			if cr.Passed {
				expectedDetected++
			} else {
				unexpectedFail++
			}
		}
		if cr.Kind == "valid" && !cr.Passed {
			unexpectedFail++
		}
		if cr.Kind == "invalid" && !cr.Passed && cr.Outcome == "admit" {
			unexpectedPass++
		}
		runRefs = append(runRefs, PCSBenchmarkReportRunRef{
			RunID:          fmt.Sprintf("bench-run-%s", cr.CaseID),
			CaseID:         cr.CaseID,
			Path:           benchmarkBundleRelPath("runs", cr.CaseID, "benchmark_run.v0.json"),
			ObservedStatus: benchmarkObservedStatus(cr),
		})
	}
	reg := coverage["registry_coverage"]
	formal := coverage["formal_check_coverage"]
	rel := coverage["release_reproducibility"]
	metricIDs := []string{
		"release_reproducibility_score",
		"failure_localization_accuracy",
		"certificate_completeness_score",
		"registry_coverage_score",
		"formal_check_coverage_score",
	}
	return PCSBenchmarkReport{
		SchemaVersion:    SchemaVersionV0,
		ReportID:         reportID,
		BenchmarkSuiteID: suiteID,
		Runs:             runRefs,
		Metrics:          metricIDs,
		MetricSummaries:  buildPCSBenchmarkReportMetricSummaries(metrics),
		ProducerID:       "provability-fabric",
		Summary: PCSBenchmarkSummary{
			TotalCases:                     total,
			PassedCases:                    passed,
			FailedCases:                    failed,
			ExpectedFailuresDetected:       expectedDetected,
			UnexpectedPasses:               unexpectedPass,
			UnexpectedFailures:             unexpectedFail,
			FailureLocalizationAccuracy:    metrics.FailureLocalizationAccuracy,
			RepairHintAccuracy:             repairHintAccuracy,
			FormalCheckCoverage:            metrics.FormalCheckEnforcementCoverage,
			RegistryCoverage:               metrics.RegistryCheckCoverage,
			ScientificMemoryRenderCoverage: 1.0,
		},
		Coverage: buildBenchmarkCoverageBlock(coverage, reg, formal, rel),
		Failures:          failures,
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestBenchmarkRun(reportID, suiteID, "report", "passed", fmt.Sprintf("%d", passed)),
	}
}
