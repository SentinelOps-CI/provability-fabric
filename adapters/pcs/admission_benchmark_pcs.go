// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"path/filepath"
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
	ObservedFailureCode          string                   `json:"observed_failure_code"`
	ObservedResponsibleComponent string                   `json:"observed_responsible_component"`
	ObservedRepairHint           string                   `json:"observed_repair_hint"`
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
	Numerator         float64        `json:"numerator"`
	Denominator       float64        `json:"denominator"`
	CoverageRatio     float64        `json:"coverage_ratio"`
	Details           map[string]any `json:"details"`
	SourceRepo        string         `json:"source_repo"`
	SourceCommit      string         `json:"source_commit"`
	SignatureOrDigest string         `json:"signature_or_digest"`
}

// PCSBenchmarkReport matches pcs-core BenchmarkReport.v0.
type PCSBenchmarkReport struct {
	SchemaVersion     string                      `json:"schema_version"`
	ReportID          string                      `json:"report_id"`
	BenchmarkSuiteID  string                      `json:"benchmark_suite_id"`
	Runs              []PCSBenchmarkReportRunRef  `json:"runs"`
	Metrics           []string                    `json:"metrics"`
	Summary           PCSBenchmarkSummary         `json:"summary"`
	Coverage          PCSBenchmarkCoverageBlock   `json:"coverage"`
	Failures          []PCSBenchmarkFailureEntry  `json:"failures"`
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
	case "scientific_memory", "ScientificMemory":
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
	fc := firstObservedFailureCode(cr.ObservedFailureCodes)
	repairHint := ""
	resp := "unknown"
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
	if ctx.VR != nil && status == "failed" {
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
		ObservedFailureCode:          fc,
		ObservedResponsibleComponent: resp,
		ObservedRepairHint:           repairHint,
		DurationMS:                   duration,
		SourceRepo:                   VerifierSourceRepo,
		SourceCommit:                 sourceCommit,
		SignatureOrDigest:            digestBenchmarkRun(runID, taskID, cr.CaseID, status, fc),
	}
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

func failureLocalizationComponents(ctx benchmarkCaseExecution) (expected, observed string) {
	expected = "verifier"
	observed = "unknown"
	wantCheck := ""
	if ctx.Case.Localization != nil {
		wantCheck = ctx.Case.Localization.CheckID
	}
	if ctx.RCVR != nil {
		for _, c := range ctx.RCVR.Checks {
			if c.Status != "failed" {
				continue
			}
			mapped := mapResponsibleComponent(c.ResponsibleComponent)
			if wantCheck == "" || c.CheckID == wantCheck {
				observed = mapped
				if wantCheck != "" {
					return expected, observed
				}
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
	if strings.Contains(strings.ToLower(firstObservedFailureCode(ctx.Case.ExpectFailureCodes)), "lean") ||
		strings.Contains(strings.ToLower(firstObservedFailureCode(ctx.Result.ObservedFailureCodes)), "lean") ||
		strings.Contains(strings.ToLower(firstObservedFailureCode(ctx.Case.ExpectFailureCodes)), "formal") {
		expected = "formal_kernel"
	}
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
	observedFC := firstObservedFailureCode(cr.ObservedFailureCodes)
	expectedResp, observedResp := failureLocalizationComponents(ctx)
	return &PCSFailureLocalizationResult{
		SchemaVersion:                SchemaVersionV0,
		ResultID:                     resultID,
		RunID:                        runID,
		CaseID:                       cr.CaseID,
		ExpectedFailureCode:          expectedFC,
		ObservedFailureCode:          observedFC,
		ExpectedResponsibleComponent: expectedResp,
		ObservedResponsibleComponent: observedResp,
		LocalizedCorrectly:           cr.FailureCodeMatch && (ctx.Loc == nil || ctx.Loc.Passed),
		SourceRepo:                   VerifierSourceRepo,
		SourceCommit:                 sourceCommit,
		SignatureOrDigest:            digestBenchmarkRun(resultID, runID, cr.CaseID, "flr", observedFC),
	}
}

func explainAdmissionError(msg string) FailureExplanation {
	fe := FailureExplanation{
		Actual:               msg,
		RepairHint:           msg,
		ResponsibleComponent: ComponentLeanTrustKernel,
		ArtifactPath:         formalCheckArtifactPath,
	}
	for _, code := range allAdmissionFailureCodes() {
		if strings.Contains(msg, code) {
			fe.FailureCode = code
			break
		}
	}
	if strings.Contains(strings.ToLower(msg), "theorem") || strings.Contains(msg, "admissible_") {
		fe.Expected = "authorized Lean theorem"
	}
	return fe
}

func explainSectionIDForRequirement(field string) string {
	switch field {
	case "failure_code", "registry_check_ref":
		return "verification"
	case "artifact_path":
		return "lineage"
	case "expected", "actual":
		return "hashes"
	case "responsible_component":
		return "provenance"
	case "repair_hint":
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
	required := []string{}
	sections := map[string]PCSExplainSectionScore{}
	gaps := []PCSExplainQualityGap{}

	var explanations []FailureExplanation
	if rcvr != nil {
		report := BuildExplainReleaseChainReport(*rcvr)
		explanations = report.Failed
	} else if vr != nil {
		explanations = ExplainVerificationFailures(*vr)
	} else if strings.TrimSpace(cr.Error) != "" {
		explanations = []FailureExplanation{explainAdmissionError(cr.Error)}
	}
	wantCheck := ""
	if c.Localization != nil {
		wantCheck = c.Localization.CheckID
	}
	var target FailureExplanation
	for _, fe := range explanations {
		if wantCheck != "" && fe.CheckID == wantCheck {
			target = fe
			break
		}
	}
	if target.CheckID == "" && len(explanations) > 0 {
		target = explanations[0]
	}

	fieldChecks := []struct {
		reqField string
		present  bool
		note     string
	}{
		{"failure_code", target.FailureCode != "", target.FailureCode},
		{"artifact_path", target.ArtifactPath != "", target.ArtifactPath},
		{"expected", target.Expected != "", target.Expected},
		{"actual", target.Actual != "", target.Actual},
		{"responsible_component", target.ResponsibleComponent != "", target.ResponsibleComponent},
		{"repair_hint", target.RepairHint != "", target.RepairHint},
		{"registry_check_ref", target.RegistryCheckRef != "", target.RegistryCheckRef},
		{"handoff_ref", target.HandoffRef != "", target.HandoffRef},
	}
	if req.FormalTheorem {
		combined := target.RepairHint + target.Actual + target.Expected
		ok := strings.Contains(combined, "theorem") || strings.Contains(combined, "admissible_") || strings.Contains(combined, "witness")
		fieldChecks = append(fieldChecks, struct {
			reqField string
			present  bool
			note     string
		}{"formal_theorem", ok, combined})
	}

	for _, fc := range fieldChecks {
		if !requirementEnabled(req, fc.reqField) {
			continue
		}
		sectionID := explainSectionIDForRequirement(fc.reqField)
		if !containsString(required, sectionID) {
			required = append(required, sectionID)
		}
		score := 0.0
		if fc.present {
			score = 1.0
		} else {
			gaps = append(gaps, PCSExplainQualityGap{
				SectionID: sectionID,
				Message:   fmt.Sprintf("missing %s in explain output", fc.reqField),
			})
		}
		prev := sections[sectionID]
		prev.Present = prev.Present || fc.present
		if score > prev.Score {
			prev.Score = score
		}
		if fc.note != "" {
			prev.Notes = fc.note
		}
		sections[sectionID] = prev
	}

	if len(required) == 0 {
		required = []string{"verification"}
		sections["verification"] = PCSExplainSectionScore{Present: false, Score: 0}
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
		SchemaVersion:         SchemaVersionV0,
		ReportID:              reportID,
		SuiteID:               suiteID,
		CaseID:                c.CaseID,
		ProducerID:            "provability-fabric",
		WorkflowID:            workflowID,
		RequiredSections:      required,
		Sections:              sections,
		SectionsPresentCount:   presentCount,
		SectionsRequiredCount:  requiredCount,
		QualityScore:          quality,
		Gaps:                  gaps,
		SourceRepo:            VerifierSourceRepo,
		SourceCommit:          sourceCommit,
		SignatureOrDigest:     digestBenchmarkRun(reportID, suiteID, c.CaseID, "explain", fmt.Sprintf("%f", quality)),
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

func buildPCSCoverageReports(
	suiteID, sourceCommit string,
	metrics BenchmarkRunMetrics,
	cov AdmissionCoverageSnapshot,
) map[string]PCSCoverageReport {
	out := map[string]PCSCoverageReport{}
	out["registry_coverage"] = PCSCoverageReport{
		SchemaVersion: SchemaVersionV0,
		CoverageID:    suiteID + "-registry",
		Metric:        "registry_coverage",
		Numerator:     metrics.RegistryCheckCoverage,
		Denominator:   1,
		CoverageRatio: metrics.RegistryCheckCoverage,
		Details: map[string]any{
			"registered_artifacts_checked": cov.RegisteredArtifactsChecked,
			"semantic_checks_executed":     cov.SemanticChecksExecuted,
			"semantic_checks_deferred":     cov.SemanticChecksDeferred,
			"semantic_checks_skipped":      cov.SemanticChecksSkipped,
		},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "registry_coverage", metrics.RegistryCheckCoverage),
	}
	out["formal_check_coverage"] = PCSCoverageReport{
		SchemaVersion: SchemaVersionV0,
		CoverageID:    suiteID + "-formal",
		Metric:        "formal_check_coverage",
		Numerator:     metrics.FormalCheckEnforcementCoverage,
		Denominator:   1,
		CoverageRatio: metrics.FormalCheckEnforcementCoverage,
		Details:       map[string]any{"formal_checks_required": cov.FormalChecksRequired},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "formal_check_coverage", metrics.FormalCheckEnforcementCoverage),
	}
	releaseRate := (metrics.ValidReleaseAdmissionRate + metrics.InvalidReleaseRejectionRate) / 2
	out["release_reproducibility"] = PCSCoverageReport{
		SchemaVersion: SchemaVersionV0,
		CoverageID:    suiteID + "-release",
		Metric:        "release_reproducibility",
		Numerator:     releaseRate,
		Denominator:   1,
		CoverageRatio: releaseRate,
		Details:       map[string]any{},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "release_reproducibility", releaseRate),
	}
	out["failure_localization"] = PCSCoverageReport{
		SchemaVersion: SchemaVersionV0,
		CoverageID:    suiteID + "-floc",
		Metric:        "failure_localization",
		Numerator:     metrics.FailureLocalizationAccuracy,
		Denominator:   1,
		CoverageRatio: metrics.FailureLocalizationAccuracy,
		Details:       map[string]any{},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "failure_localization", metrics.FailureLocalizationAccuracy),
	}
	out["certificate_completeness"] = PCSCoverageReport{
		SchemaVersion: SchemaVersionV0,
		CoverageID:    suiteID + "-cert",
		Metric:        "certificate_completeness",
		Numerator:     metrics.FailureCodeAccuracy,
		Denominator:   1,
		CoverageRatio: metrics.FailureCodeAccuracy,
		Details:       map[string]any{},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "certificate_completeness", metrics.FailureCodeAccuracy),
	}
	return out
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
			Path:           filepath.Join("runs", cr.CaseID, "benchmark_run.v0.json"),
			ObservedStatus: benchmarkObservedStatus(cr),
		})
	}
	reg := coverage["registry_coverage"]
	formal := coverage["formal_check_coverage"]
	rel := coverage["release_reproducibility"]
	return PCSBenchmarkReport{
		SchemaVersion:    SchemaVersionV0,
		ReportID:         reportID,
		BenchmarkSuiteID: suiteID,
		Runs:             runRefs,
		Metrics: []string{
			"release_reproducibility",
			"failure_localization",
			"certificate_completeness",
			"registry_coverage",
			"formal_check_coverage",
		},
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
