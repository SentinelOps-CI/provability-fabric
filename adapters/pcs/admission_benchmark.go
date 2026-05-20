// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"
)

// AdmissionBenchmarkCase is admission_benchmark_case.v0 under benchmarks/admission/<workflow>/.
type AdmissionBenchmarkCase struct {
	CaseID              string   `json:"case_id"`
	Workflow            string   `json:"workflow"`
	Kind                string   `json:"kind"` // valid | invalid
	ProfileID           string   `json:"profile_id"`
	Expect              string   `json:"expect"` // admit | reject
	ExpectFailureCodes  []string `json:"expect_failure_codes,omitempty"`
	VerifyMode          string   `json:"verify_mode"` // science_claim | release_chain | admission_gate
	Inputs              AdmissionBenchmarkInputs `json:"inputs"`
	Localization        *AdmissionBenchmarkLocalization `json:"localization,omitempty"`
	ExplainRequirements *AdmissionBenchmarkExplainReq `json:"explain_requirements,omitempty"`
}

// AdmissionBenchmarkWorkflow is workflow.json defaults for a benchmark suite.
type AdmissionBenchmarkWorkflow struct {
	WorkflowID  string                        `json:"workflow_id"`
	ProfileID   string                        `json:"profile_id"`
	FixtureRoot string                        `json:"fixture_root"`
	Defaults    AdmissionBenchmarkInputs      `json:"defaults"`
}

type AdmissionBenchmarkInputs struct {
	Bundle            string `json:"bundle,omitempty"`
	Handoff           string `json:"handoff,omitempty"`
	Registry          string `json:"registry,omitempty"`
	Manifest          string `json:"manifest,omitempty"`
	ArtifactDir       string `json:"artifact_dir,omitempty"`
	ProofObligations  string `json:"proof_obligations,omitempty"`
	LeanCheckResult    string `json:"lean_check_result,omitempty"`
	OmitHandoff          bool `json:"omit_handoff,omitempty"`
	OmitRegistry         bool `json:"omit_registry,omitempty"`
	OmitFormal           bool `json:"omit_formal,omitempty"`
	OmitProofObligations bool `json:"omit_proof_obligations,omitempty"`
	OmitLeanCheckResult  bool `json:"omit_lean_check_result,omitempty"`
}

type AdmissionBenchmarkLocalization struct {
	CheckID      string `json:"check_id,omitempty"`
	ArtifactPath string `json:"artifact_path,omitempty"`
}

type AdmissionBenchmarkExplainReq struct {
	FailureCode          bool `json:"failure_code,omitempty"`
	ArtifactPath         bool `json:"artifact_path,omitempty"`
	Expected             bool `json:"expected,omitempty"`
	Actual               bool `json:"actual,omitempty"`
	ResponsibleComponent bool `json:"responsible_component,omitempty"`
	RepairHint           bool `json:"repair_hint,omitempty"`
	RegistryCheckRef     bool `json:"registry_check_ref,omitempty"`
	HandoffRef           bool `json:"handoff_ref,omitempty"`
	FormalTheorem        bool `json:"formal_theorem,omitempty"`
}

// AdmissionBenchmarkOptions configures a benchmark run.
type AdmissionBenchmarkOptions struct {
	RepoRoot         string
	CasesDir         string
	BenchmarkRoot    string
	RegistryPath     string
	SourceCommit     string
	ValidatorVersion string
	OutDir           string
	RunID            string
	ValidateBundle   bool // re-validate bundle after write (pcs validate gate)
}

// AdmissionBenchmarkCaseResult is one executed case outcome.
type AdmissionBenchmarkCaseResult struct {
	CaseID                 string   `json:"case_id"`
	Kind                   string   `json:"kind"`
	Expect                 string   `json:"expect"`
	Outcome                string   `json:"outcome"` // admit | reject | error
	Passed                 bool     `json:"passed"`
	ObservedFailureCodes   []string `json:"observed_failure_codes,omitempty"`
	ExpectFailureCodes     []string `json:"expect_failure_codes,omitempty"`
	FailureCodeMatch       bool     `json:"failure_code_match"`
	LocalizationMatch      bool     `json:"localization_match"`
	ExplainCompleteness    float64  `json:"explain_completeness"`
	VerificationStatus     string   `json:"verification_status,omitempty"`
	ReleaseChainStatus     string   `json:"release_chain_status,omitempty"`
	Error                  string   `json:"error,omitempty"`
	ReleaseChainResultPath string   `json:"release_chain_result_path,omitempty"`
}

// AdmissionBenchmarkSuiteV0 is the PF-internal suite summary (metrics + case outcomes).
// pcs-bench consumes per-case BenchmarkRun.v0 and BenchmarkReport.v0 from the output bundle.
type AdmissionBenchmarkSuiteV0 struct {
	SchemaVersion string                     `json:"schema_version"`
	RunID         string                     `json:"run_id"`
	Workflow      string                     `json:"workflow"`
	ProfileID     string                     `json:"profile_id"`
	StartedAt     string                     `json:"started_at"`
	CompletedAt   string                     `json:"completed_at"`
	Metrics       BenchmarkRunMetrics        `json:"metrics"`
	Cases         []AdmissionBenchmarkCaseResult `json:"cases"`
}

// BenchmarkRunMetrics aggregates admission benchmark scores.
type BenchmarkRunMetrics struct {
	ValidReleaseAdmissionRate       float64 `json:"valid_release_admission_rate"`
	InvalidReleaseRejectionRate     float64 `json:"invalid_release_rejection_rate"`
	FailureLocalizationAccuracy     float64 `json:"failure_localization_accuracy"`
	FailureCodeAccuracy             float64 `json:"failure_code_accuracy"`
	ExplainOutputCompleteness       float64 `json:"explain_output_completeness"`
	RegistryCheckCoverage           float64 `json:"registry_check_coverage"`
	AdmissionProfileCoverage        float64 `json:"admission_profile_coverage"`
	FormalCheckEnforcementCoverage  float64 `json:"formal_check_enforcement_coverage"`
}

// FailureLocalizationResultV0 summarizes localization scoring.
type FailureLocalizationResultV0 struct {
	SchemaVersion string                          `json:"schema_version"`
	RunID         string                          `json:"run_id"`
	Workflow      string                          `json:"workflow"`
	Cases         []FailureLocalizationCaseResult `json:"cases"`
}

type FailureLocalizationCaseResult struct {
	CaseID            string `json:"case_id"`
	ExpectedCheckID   string `json:"expected_check_id,omitempty"`
	ObservedCheckID   string `json:"observed_check_id,omitempty"`
	ArtifactPathMatch bool   `json:"artifact_path_match"`
	Passed            bool   `json:"passed"`
}

// CoverageReportV0 is coverage_report.v0 for registry/profile/formal admission coverage.
type CoverageReportV0 struct {
	SchemaVersion string              `json:"schema_version"`
	RunID         string              `json:"run_id"`
	Workflow      string              `json:"workflow"`
	Registry      RegistryCoverage    `json:"registry"`
	Admission     AdmissionCoverage   `json:"admission"`
	Formal        FormalCoverage      `json:"formal"`
}

type RegistryCoverage struct {
	RegisteredArtifactsChecked int `json:"registered_artifacts_checked"`
	RequiredFieldsChecked      int `json:"required_fields_checked"`
	AllowedStatusesChecked     int `json:"allowed_statuses_checked"`
	SemanticChecksExecuted     int `json:"semantic_checks_executed"`
	SemanticChecksDeferred     int `json:"semantic_checks_deferred"`
	SemanticChecksSkipped      int `json:"semantic_checks_skipped"`
	ReleaseBlockingPassed      int `json:"release_blocking_checks_passed"`
	ReleaseBlockingFailed      int `json:"release_blocking_checks_failed"`
}

type AdmissionCoverage struct {
	ProfilesExercised      []string `json:"profiles_exercised"`
	RegistryChecksRequired []string `json:"registry_checks_required"`
	RegistryChecksObserved []string `json:"registry_checks_observed"`
}

type FormalCoverage struct {
	FormalChecksRequired   bool     `json:"formal_checks_required"`
	ObligationKindsChecked []string `json:"obligation_kinds_checked"`
	FormalCheckIDsObserved []string `json:"formal_check_ids_observed"`
}

// ExplainQualityReportV0 scores pf explain release-chain output per invalid case.
type ExplainQualityReportV0 struct {
	SchemaVersion string                    `json:"schema_version"`
	RunID         string                    `json:"run_id"`
	Workflow      string                    `json:"workflow"`
	Cases         []ExplainQualityCaseScore `json:"cases"`
	MeanCompleteness float64                `json:"mean_completeness"`
}

type ExplainQualityCaseScore struct {
	CaseID       string             `json:"case_id"`
	Completeness float64            `json:"completeness"`
	Fields       map[string]bool    `json:"fields"`
}

// BenchmarkRunV0 is an alias kept for tests and CLI metrics display.
type BenchmarkRunV0 = AdmissionBenchmarkSuiteV0

// RunAdmissionBenchmark executes all cases under casesDir and writes a pcs-core benchmark bundle to OutDir.
func RunAdmissionBenchmark(opts AdmissionBenchmarkOptions) (AdmissionBenchmarkSuiteV0, FailureLocalizationResultV0, CoverageReportV0, ExplainQualityReportV0, error) {
	if strings.TrimSpace(opts.CasesDir) == "" {
		return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, fmt.Errorf("cases directory is required")
	}
	workflowPath := filepath.Join(opts.CasesDir, "workflow.json")
	workflowData, err := os.ReadFile(workflowPath)
	if err != nil {
		return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, fmt.Errorf("read workflow.json: %w", err)
	}
	var workflow AdmissionBenchmarkWorkflow
	if err := json.Unmarshal(workflowData, &workflow); err != nil {
		return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, fmt.Errorf("parse workflow.json: %w", err)
	}
	cases, err := loadAdmissionBenchmarkCases(opts.CasesDir, workflow)
	if err != nil {
		return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, err
	}
	opts.BenchmarkRoot = opts.CasesDir
	if len(cases) == 0 {
		return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, fmt.Errorf("no benchmark cases found under %s", opts.CasesDir)
	}

	started := time.Now().UTC()
	runID := opts.RunID
	if runID == "" {
		runID = fmt.Sprintf("benchmark-%s-%d", workflow.WorkflowID, started.Unix())
	}
	if opts.ValidatorVersion == "" {
		opts.ValidatorVersion = DefaultVerifierVersion
	}
	if opts.SourceCommit == "" {
		opts.SourceCommit = ResolveSourceCommit()
	}

	var results []AdmissionBenchmarkCaseResult
	var locCases []FailureLocalizationCaseResult
	var explainCases []ExplainQualityCaseScore
	var lastRCVR *ReleaseChainValidationResult
	var executions []benchmarkCaseExecution
	suiteID := suiteIDFromWorkflow(workflow.WorkflowID)
	taskID := taskIDFromWorkflow(workflow.WorkflowID)

	for _, c := range cases {
		profileID := c.ProfileID
		if profileID == "" {
			profileID = workflow.ProfileID
		}
		profile, err := LoadAdmissionProfile(profileID)
		if err != nil {
			return AdmissionBenchmarkSuiteV0{}, FailureLocalizationResultV0{}, CoverageReportV0{}, ExplainQualityReportV0{}, err
		}
		started := time.Now()
		cr, rcvr, vr, loc, explain := executeAdmissionBenchmarkCase(opts, workflow, profile, c, opts.CasesDir)
		completed := time.Now()
		cmd := buildBenchmarkCommandLine(c, workflow, opts)
		exitCode := 0
		if !cr.Passed {
			exitCode = 1
		}
		pcsExplain := ExportPCSExplainQualityReport(ExportPCSExplainQualityCaseInput{
			Case: c, Result: cr, RCVR: rcvr, VR: vr,
			SuiteID: suiteID, WorkflowID: workflow.WorkflowID, SourceCommit: opts.SourceCommit,
		})
		if pcsExplain != nil {
			explain = explainFromPCSReport(pcsExplain)
			cr.ExplainCompleteness = pcsExplain.QualityScore
		}
		cr.Passed = admissionCasePassed(c, cr, pcsExplain)
		if pcsExplain == nil && explain == nil && c.ExplainRequirements != nil {
			explain = scoreExplainQualityLegacy(c, rcvr, vr)
		}
		executions = append(executions, benchmarkCaseExecution{
			Case: c, Result: cr, RCVR: rcvr, VR: vr, Loc: loc, Explain: explain,
			PCSExplain: pcsExplain, Started: started, Completed: completed,
			Command: cmd, ExitCode: exitCode,
			LogLines: []string{fmt.Sprintf("case=%s outcome=%s passed=%v", cr.CaseID, cr.Outcome, cr.Passed)},
		})
		results = append(results, cr)
		if loc != nil {
			locCases = append(locCases, *loc)
		}
		if explain != nil {
			explainCases = append(explainCases, *explain)
		}
		if rcvr != nil && c.Kind == "valid" {
			lastRCVR = rcvr
		}
	}

	baseProfile, _ := LoadAdmissionProfile(workflow.ProfileID)
	covReport := buildCoverageReport(runID, workflow, baseProfile, lastRCVR)
	metrics := enrichBenchmarkMetrics(computeBenchmarkMetrics(results, explainCases), covReport, results)
	run := AdmissionBenchmarkSuiteV0{
		SchemaVersion: SchemaVersionV0,
		RunID:         runID,
		Workflow:      workflow.WorkflowID,
		ProfileID:     workflow.ProfileID,
		StartedAt:     started.Format(time.RFC3339),
		CompletedAt:   time.Now().UTC().Format(time.RFC3339),
		Metrics:       metrics,
		Cases:         results,
	}
	if locCases == nil {
		locCases = []FailureLocalizationCaseResult{}
	}
	if explainCases == nil {
		explainCases = []ExplainQualityCaseScore{}
	}
	locReport := FailureLocalizationResultV0{
		SchemaVersion: SchemaVersionV0,
		RunID:         runID,
		Workflow:      workflow.WorkflowID,
		Cases:         locCases,
	}
	explainReport := ExplainQualityReportV0{
		SchemaVersion: SchemaVersionV0,
		RunID:         runID,
		Workflow:      workflow.WorkflowID,
		Cases:         explainCases,
		MeanCompleteness: metrics.ExplainOutputCompleteness,
	}

	repoRoot := opts.RepoRoot
	if repoRoot == "" {
		repoRoot, _ = FindRepoRoot(opts.CasesDir)
	}
	if opts.OutDir != "" {
		covSnap := admissionCoverageSnapshotFromInternal(covReport)
		bundle, err := assemblePCSBenchmarkBundle(runID, suiteID, taskID, workflow, opts, executions, metrics, covSnap)
		if err != nil {
			return run, locReport, covReport, explainReport, err
		}
		bundle.InternalSuite = run
		if err := writeAdmissionBenchmarkBundle(repoRoot, opts.OutDir, bundle, executions); err != nil {
			return run, locReport, covReport, explainReport, err
		}
		if opts.ValidateBundle {
			if err := ValidateAdmissionBenchmarkBundleDir(repoRoot, opts.OutDir); err != nil {
				return run, locReport, covReport, explainReport, fmt.Errorf("benchmark bundle validation: %w", err)
			}
		}
	}
	return run, locReport, covReport, explainReport, nil
}

func admissionCasePassed(c AdmissionBenchmarkCase, cr AdmissionBenchmarkCaseResult, pcsExplain *PCSExplainQualityReport) bool {
	base := outcomeMatchesExpect(c.Expect, cr.Outcome) && cr.FailureCodeMatch
	if c.Localization != nil {
		base = base && cr.LocalizationMatch
	}
	if c.Kind == "invalid" && c.ExplainRequirements != nil {
		if pcsExplain == nil {
			return false
		}
		return base && pcsExplain.QualityScore >= 0.8
	}
	return base
}

func buildBenchmarkCommandLine(c AdmissionBenchmarkCase, workflow AdmissionBenchmarkWorkflow, opts AdmissionBenchmarkOptions) string {
	parts := []string{"pf", "benchmark", "admission", "--cases", opts.CasesDir}
	if opts.RegistryPath != "" {
		parts = append(parts, "--registry", opts.RegistryPath)
	}
	parts = append(parts, fmt.Sprintf("# case=%s mode=%s profile=%s", c.CaseID, c.VerifyMode, c.ProfileID))
	_ = workflow
	return strings.Join(parts, " ")
}

func explainFromPCSReport(r *PCSExplainQualityReport) *ExplainQualityCaseScore {
	if r == nil {
		return nil
	}
	fields := map[string]bool{}
	for id, sec := range r.Sections {
		fields[id] = sec.Present
	}
	return &ExplainQualityCaseScore{
		CaseID:       r.CaseID,
		Completeness: r.QualityScore,
		Fields:       fields,
	}
}

func scoreExplainQualityLegacy(c AdmissionBenchmarkCase, rcvr *ReleaseChainValidationResult, vr *VerificationResult) *ExplainQualityCaseScore {
	if rcvr != nil {
		return scoreExplainQuality(c, *rcvr)
	}
	if vr != nil {
		return scoreExplainQualityFromVerification(c, *vr)
	}
	return nil
}

func scoreExplainQualityFromVerification(c AdmissionBenchmarkCase, vr VerificationResult) *ExplainQualityCaseScore {
	req := c.ExplainRequirements
	if req == nil {
		return nil
	}
	explanations := ExplainVerificationFailures(vr)
	var target FailureExplanation
	if len(explanations) > 0 {
		target = explanations[0]
	}
	fields := map[string]bool{}
	var score, total float64
	check := func(required bool, present bool, name string) {
		if !required {
			return
		}
		total++
		fields[name] = present
		if present {
			score++
		}
	}
	check(req.FailureCode, target.FailureCode != "", "failure_code")
	check(req.ArtifactPath, target.ArtifactPath != "", "artifact_path")
	check(req.Expected, target.Expected != "", "expected")
	check(req.Actual, target.Actual != "", "actual")
	check(req.ResponsibleComponent, target.ResponsibleComponent != "", "responsible_component")
	check(req.RepairHint, target.RepairHint != "", "repair_hint")
	check(req.RegistryCheckRef, target.RegistryCheckRef != "", "registry_check_ref")
	check(req.HandoffRef, target.HandoffRef != "", "handoff_ref")
	if req.FormalTheorem {
		combined := target.RepairHint + target.Actual + target.Expected
		check(true, strings.Contains(combined, "theorem") || strings.Contains(combined, "admissible_") || strings.Contains(combined, "witness"), "formal_theorem")
	}
	completeness := 1.0
	if total > 0 {
		completeness = score / total
	}
	return &ExplainQualityCaseScore{CaseID: c.CaseID, Completeness: completeness, Fields: fields}
}

func admissionCoverageSnapshotFromInternal(cov CoverageReportV0) AdmissionCoverageSnapshot {
	return AdmissionCoverageSnapshot{
		RegisteredArtifactsChecked: cov.Registry.RegisteredArtifactsChecked,
		SemanticChecksExecuted:     cov.Registry.SemanticChecksExecuted,
		SemanticChecksDeferred:     cov.Registry.SemanticChecksDeferred,
		SemanticChecksSkipped:      cov.Registry.SemanticChecksSkipped,
		FormalChecksRequired:       cov.Formal.FormalChecksRequired,
	}
}

func assemblePCSBenchmarkBundle(
	runID, suiteID, taskID string,
	workflow AdmissionBenchmarkWorkflow,
	opts AdmissionBenchmarkOptions,
	executions []benchmarkCaseExecution,
	metrics BenchmarkRunMetrics,
	cov AdmissionCoverageSnapshot,
) (PCSBenchmarkBundle, error) {
	var runs []PCSBenchmarkRun
	flrs := []PCSFailureLocalizationResult{}
	explains := []PCSExplainQualityReport{}
	var commands []PCSBenchmarkCommandEntry
	for _, ex := range executions {
		run := buildPCSBenchmarkRun(ex, suiteID, taskID, opts.SourceCommit)
		runs = append(runs, run)
		commands = append(commands, run.Commands...)
		if flr := buildPCSFailureLocalization(ex, taskID, opts.SourceCommit); flr != nil {
			flrs = append(flrs, *flr)
		}
		if ex.PCSExplain != nil {
			explains = append(explains, *ex.PCSExplain)
		}
	}
	coverage := buildPCSCoverageReports(suiteID, opts.SourceCommit, metrics, cov)
	report := buildPCSBenchmarkReport(suiteID, runID, opts.SourceCommit, executions, metrics, coverage)
	return PCSBenchmarkBundle{
		Report:               report,
		Runs:                 runs,
		FailureLocalizations: flrs,
		ExplainQuality:       explains,
		CoverageByMetric:     coverage,
		Commands:             commands,
	}, nil
}

func loadAdmissionBenchmarkCases(casesDir string, workflow AdmissionBenchmarkWorkflow) ([]AdmissionBenchmarkCase, error) {
	var cases []AdmissionBenchmarkCase
	for _, sub := range []string{"valid", "invalid"} {
		dir := filepath.Join(casesDir, sub)
		entries, err := os.ReadDir(dir)
		if err != nil {
			if os.IsNotExist(err) {
				continue
			}
			return nil, err
		}
		for _, e := range entries {
			if e.IsDir() || !strings.HasSuffix(e.Name(), ".json") {
				continue
			}
			data, err := os.ReadFile(filepath.Join(dir, e.Name()))
			if err != nil {
				return nil, err
			}
			var c AdmissionBenchmarkCase
			if err := json.Unmarshal(data, &c); err != nil {
				return nil, fmt.Errorf("parse %s: %w", e.Name(), err)
			}
			if c.CaseID == "" {
				c.CaseID = strings.TrimSuffix(e.Name(), ".json")
			}
			if c.Workflow == "" {
				c.Workflow = workflow.WorkflowID
			}
			if c.ProfileID == "" {
				c.ProfileID = workflow.ProfileID
			}
			if c.Kind == "" {
				c.Kind = sub
			}
			if repoRoot, err := FindRepoRoot(casesDir); err == nil {
				if err := ValidateAdmissionBenchmarkCase(repoRoot, c); err != nil {
					return nil, fmt.Errorf("%s/%s: %w", sub, e.Name(), err)
				}
			}
			cases = append(cases, c)
		}
	}
	sort.Slice(cases, func(i, j int) bool { return cases[i].CaseID < cases[j].CaseID })
	return cases, nil
}

func executeAdmissionBenchmarkCase(
	opts AdmissionBenchmarkOptions,
	workflow AdmissionBenchmarkWorkflow,
	profile *AdmissionProfile,
	c AdmissionBenchmarkCase,
	casesDir string,
) (AdmissionBenchmarkCaseResult, *ReleaseChainValidationResult, *VerificationResult, *FailureLocalizationCaseResult, *ExplainQualityCaseScore) {
	cr := AdmissionBenchmarkCaseResult{
		CaseID:             c.CaseID,
		Kind:               c.Kind,
		Expect:             c.Expect,
		ExpectFailureCodes: append([]string(nil), c.ExpectFailureCodes...),
	}
	in := mergeBenchmarkInputs(workflow, c.Inputs)
	repoRoot := opts.RepoRoot
	if repoRoot == "" {
		repoRoot, _ = FindRepoRoot(opts.CasesDir)
	}
	benchRoot := opts.BenchmarkRoot
	if benchRoot == "" {
		benchRoot = casesDir
	}
	resolve := func(p string) string {
		return resolveBenchmarkPath(repoRoot, workflow.FixtureRoot, benchRoot, p)
	}
	bundlePath := resolve(in.Bundle)
	registryPath := opts.RegistryPath
	if strings.TrimSpace(in.Registry) != "" {
		registryPath = resolve(in.Registry)
	}
	var handoff *LoadedHandoff
	if !in.OmitHandoff && strings.TrimSpace(in.Handoff) != "" {
		loaded, err := LoadHandoff(resolve(in.Handoff))
		if err != nil {
			cr.Outcome = "error"
			cr.Error = err.Error()
			cr.Passed = false
			return cr, nil, nil, nil, nil
		}
		handoff = loaded
	}
	var registry *ArtifactRegistry
	if !in.OmitRegistry && registryPath != "" {
		reg, err := LoadArtifactRegistry(registryPath)
		if err != nil {
			cr.Outcome = "error"
			cr.Error = err.Error()
			cr.Passed = false
			return cr, nil, nil, nil, nil
		}
		registry = reg
	}
	var manifest *ReleaseManifest
	if strings.TrimSpace(in.Manifest) != "" {
		m, err := LoadReleaseManifest(resolve(in.Manifest))
		if err != nil {
			cr.Outcome = "error"
			cr.Error = err.Error()
			cr.Passed = false
			return cr, nil, nil, nil, nil
		}
		manifest = m
	}
	var vr *VerificationResult
	formal := FormalCheckInputs{}
	if !in.OmitFormal {
		if !in.OmitProofObligations && strings.TrimSpace(in.ProofObligations) != "" {
			formal.ProofObligationsPath = resolve(in.ProofObligations)
		}
		if !in.OmitLeanCheckResult && strings.TrimSpace(in.LeanCheckResult) != "" {
			formal.LeanCheckResultPath = resolve(in.LeanCheckResult)
		}
		formal, _ = ResolveFormalCheckInputs(repoRoot, formal)
	}
	releaseMode := strings.TrimSpace(c.VerifyMode) != "admission_gate"
	if in.OmitHandoff && c.Kind == "invalid" && strings.TrimSpace(c.VerifyMode) == "science_claim" && !expectsReleaseAdmissionFailure(c) {
		releaseMode = false
	}
	policy := ReleaseAdmissionPolicy{ReleaseMode: releaseMode, AllowMissingHandoff: in.OmitHandoff}
	var err error
	var rcvr *ReleaseChainValidationResult

	switch strings.TrimSpace(c.VerifyMode) {
	case "admission_gate":
		err = EnforceScienceClaimAdmission(policy, handoff, registry, profile)
		if err == nil {
			err = EnforceFormalCheckAdmission(profile, manifest, policy, formal)
		}
		if err == nil && bundlePath != "" {
			bundle, loadErr := LoadScienceClaimBundle(bundlePath)
			if loadErr == nil {
				err = EnforceAdmissionProfile(profile, bundlePath, bundle, handoff, releaseMode)
			} else {
				err = loadErr
			}
		}
	case "release_chain":
		artifactDir := resolve(in.ArtifactDir)
		if artifactDir == "" && strings.TrimSpace(in.Manifest) != "" {
			artifactDir = filepath.Dir(resolve(in.Manifest))
		}
		if err = EnforceReleaseChainAdmission(policy, resolve(in.Manifest), registry); err == nil {
			err = EnforceFormalCheckAdmission(profile, manifest, policy, formal)
		}
		if err == nil {
			rcOpts := ReleaseChainVerifyOptions{
				RepoRoot:         repoRoot,
				ArtifactDir:      artifactDir,
				ValidatorVersion: opts.ValidatorVersion,
				SourceCommit:     opts.SourceCommit,
				ReleaseMode:      true,
				Registry:         registry,
				AdmissionProfile: profile,
				FormalChecks:     formal,
			}
			var rcResult ReleaseChainValidationResult
			rcResult, err = VerifyReleaseChainFromManifest(resolve(in.Manifest), rcOpts)
			rcvr = &rcResult
			cr.ReleaseChainStatus = rcResult.Status
			if err == nil && rcResult.Status == StatusRejected {
				err = fmt.Errorf("release chain status %s", rcResult.Status)
				cr.ObservedFailureCodes = failureCodesFromRCVR(rcResult)
			}
		}
	default: // science_claim
		if err = EnforceScienceClaimAdmission(policy, handoff, registry, profile); err == nil {
			err = EnforceFormalCheckAdmission(profile, manifest, policy, formal)
		}
		if err == nil && bundlePath != "" {
			bundle, loadErr := LoadScienceClaimBundle(bundlePath)
			if loadErr != nil {
				err = loadErr
			} else if profile.IsComputationProfile() {
				if admErr := EnforceAdmissionProfile(profile, bundlePath, bundle, handoff, releaseMode); admErr != nil {
					err = admErr
				} else {
					vrResult := BuildComputationVerificationResult(bundle, ValidateOptions{ReleaseMode: releaseMode, Registry: registry})
					vr = &vrResult
					cr.VerificationStatus = vrResult.Status
					if !VerificationPassed(vrResult) {
						err = fmt.Errorf("verification status %s", vrResult.Status)
						cr.ObservedFailureCodes = failureCodesFromVerification(vrResult)
					}
				}
			} else if profile.IsToolUseProfile() {
				if admErr := EnforceAdmissionProfile(profile, bundlePath, bundle, handoff, releaseMode); admErr != nil {
					err = admErr
				} else {
					err = fmt.Errorf("%s: full tool-use bundle verification is not implemented yet", FailureCodeToolUseReleaseNotImplemented)
				}
			} else {
				vOpts := ValidateOptions{
					RepoRoot:            repoRoot,
					VerifierVersion:     opts.ValidatorVersion,
					SourceCommit:        opts.SourceCommit,
					ReleaseMode:         releaseMode,
					AllowMissingHandoff: in.OmitHandoff,
					Handoff:             handoff,
					Registry:            registry,
					AdmissionProfile:    profile,
					ReleaseManifest:     manifest,
					FormalChecks:        formal,
				}
				var vrResult VerificationResult
				vrResult, err = VerifyScienceClaimBundle(bundlePath, bundle, vOpts)
				vr = &vrResult
				cr.VerificationStatus = vrResult.Status
				if err == nil && !VerificationPassed(vrResult) {
					err = fmt.Errorf("verification status %s", vrResult.Status)
					cr.ObservedFailureCodes = failureCodesFromVerification(vrResult)
				}
			}
		}
	}

	if len(cr.ObservedFailureCodes) == 0 {
		cr.ObservedFailureCodes = failureCodesFromError(err)
	}
	if err != nil {
		cr.Outcome = "reject"
		cr.Error = err.Error()
	} else {
		cr.Outcome = "admit"
	}
	cr.FailureCodeMatch = failureCodesMatch(c.ExpectFailureCodes, cr.ObservedFailureCodes)
	cr.Passed = outcomeMatchesExpect(c.Expect, cr.Outcome) && cr.FailureCodeMatch

	var loc *FailureLocalizationCaseResult
	if c.Localization != nil && rcvr != nil {
		loc = scoreLocalization(c, *rcvr)
		cr.LocalizationMatch = loc.Passed
		if c.Kind == "invalid" {
			cr.Passed = cr.Passed && loc.Passed
		}
		cr.ObservedFailureCodes = uniqueStrings(append(cr.ObservedFailureCodes, failureCodesFromRCVR(*rcvr)...))
		cr.FailureCodeMatch = failureCodesMatch(c.ExpectFailureCodes, cr.ObservedFailureCodes)
	} else if c.Localization != nil && err != nil {
		loc = &FailureLocalizationCaseResult{
			CaseID:          c.CaseID,
			ExpectedCheckID: c.Localization.CheckID,
			Passed:          cr.FailureCodeMatch,
		}
		cr.LocalizationMatch = loc.Passed
	}

	var explain *ExplainQualityCaseScore
	if c.ExplainRequirements != nil && rcvr != nil && rcvr.Status == StatusRejected {
		explain = scoreExplainQuality(c, *rcvr)
		cr.ExplainCompleteness = explain.Completeness
	} else if c.ExplainRequirements != nil && vr != nil && !VerificationPassed(*vr) {
		explain = scoreExplainQualityFromVerification(c, *vr)
		cr.ExplainCompleteness = explain.Completeness
	}
	return cr, rcvr, vr, loc, explain
}

func mergeBenchmarkInputs(workflow AdmissionBenchmarkWorkflow, overrides AdmissionBenchmarkInputs) AdmissionBenchmarkInputs {
	out := workflow.Defaults
	if overrides.Bundle != "" {
		out.Bundle = overrides.Bundle
	}
	if overrides.Handoff != "" {
		out.Handoff = overrides.Handoff
	}
	if overrides.Registry != "" {
		out.Registry = overrides.Registry
	}
	if overrides.Manifest != "" {
		out.Manifest = overrides.Manifest
	}
	if overrides.ArtifactDir != "" {
		out.ArtifactDir = overrides.ArtifactDir
	}
	if overrides.ProofObligations != "" {
		out.ProofObligations = overrides.ProofObligations
	}
	if overrides.LeanCheckResult != "" {
		out.LeanCheckResult = overrides.LeanCheckResult
	}
	if overrides.OmitHandoff {
		out.OmitHandoff = true
	}
	if overrides.OmitRegistry {
		out.OmitRegistry = true
	}
	if overrides.OmitFormal {
		out.OmitFormal = true
	}
	if overrides.OmitProofObligations {
		out.OmitProofObligations = true
	}
	if overrides.OmitLeanCheckResult {
		out.OmitLeanCheckResult = true
	}
	return out
}

func resolveBenchmarkPath(repoRoot, fixtureRoot, benchmarkRoot, ref string) string {
	ref = strings.TrimSpace(ref)
	if ref == "" {
		return ""
	}
	ref = strings.ReplaceAll(ref, "${repo}", repoRoot)
	if filepath.IsAbs(ref) {
		return ref
	}
	if strings.HasPrefix(ref, "tests/") || strings.HasPrefix(ref, "benchmarks/") {
		return filepath.Join(repoRoot, filepath.FromSlash(ref))
	}
	if strings.HasPrefix(ref, "support/") && benchmarkRoot != "" {
		return filepath.Join(benchmarkRoot, filepath.FromSlash(ref))
	}
	if fixtureRoot != "" {
		root := strings.ReplaceAll(fixtureRoot, "${repo}", repoRoot)
		return filepath.Join(root, ref)
	}
	return filepath.Join(repoRoot, ref)
}

func failureCodesFromVerification(vr VerificationResult) []string {
	var codes []string
	for _, c := range FailedChecks(vr) {
		if rc, ok := c.Details["reason_code"].(string); ok && rc != "" {
			codes = append(codes, rc)
		}
		if strings.Contains(c.CheckID, "trace_hash") {
			codes = append(codes, ReasonTraceHashMismatch)
		}
		if strings.Contains(c.CheckID, "certificate") {
			codes = append(codes, ReasonCertificateRejected)
		}
	}
	return uniqueStrings(codes)
}

func failureCodesFromRCVR(rcvr ReleaseChainValidationResult) []string {
	var codes []string
	for _, fc := range rcvr.FailureCodes {
		if fc != "" {
			codes = append(codes, fc)
		}
	}
	for _, c := range rcvr.Checks {
		if c.Status != "failed" {
			continue
		}
		if c.CheckID != "" {
			codes = append(codes, c.CheckID)
		}
		if fc, ok := c.Details["failure_code"].(string); ok && fc != "" {
			codes = append(codes, fc)
		}
	}
	return uniqueStrings(codes)
}

func failureCodesFromError(err error) []string {
	if err == nil {
		return nil
	}
	msg := err.Error()
	var codes []string
	for _, code := range allAdmissionFailureCodes() {
		if strings.Contains(msg, code) {
			codes = append(codes, code)
		}
	}
	if len(codes) == 0 && strings.Contains(msg, ReasonTraceHashMismatch) {
		codes = append(codes, ReasonTraceHashMismatch)
	}
	if len(codes) == 0 && strings.Contains(msg, ReasonCertificateRejected) {
		codes = append(codes, ReasonCertificateRejected)
	}
	if len(codes) == 0 && (strings.Contains(msg, "producer mismatch") || strings.Contains(msg, "not allowed for")) {
		codes = append(codes, ReasonRegistryAdmissionFailed)
	}
	sort.Strings(codes)
	return uniqueStrings(codes)
}

func allAdmissionFailureCodes() []string {
	return []string{
		ReasonTraceHashMismatch,
		ReasonCertificateRejected,
		ReasonCertificateNotChecked,
		ReasonRegistryAdmissionFailed,
		FailureCodeReleaseModeHandoffRequired,
		FailureCodeReleaseModeRegistryRequired,
		FailureCodeReleaseModeManifestRequired,
		FailureCodeLegacyHandoffForbiddenInReleaseMode,
		FailureCodeMissingAdmissionProfile,
		FailureCodeUnknownAdmissionProfile,
		FailureCodeAdmissionProfileWorkflowMismatch,
		FailureCodeAdmissionProfileRequiredArtifactMissing,
		FailureCodeMissingToolUseTrace,
		FailureCodeMissingToolUseCertificate,
		FailureCodeToolUseCertificateRejected,
		FailureCodeToolTraceHashMismatch,
		FailureCodePolicyHashMismatch,
		FailureCodeUnauthorizedToolCallViolation,
		FailureCodeToolUseReleaseNotImplemented,
		FailureCodeMissingDatasetReceipt,
		FailureCodeMissingEnvironmentReceipt,
		FailureCodeMissingComputationWitness,
		FailureCodeRejectedComputationWitness,
		FailureCodeResultHashMismatch,
		FailureCodeDatasetHashMismatch,
		FailureCodeMissingCodeCommit,
		FailureCodeNonzeroExitCode,
		FailureCodeEnvironmentDigestMismatch,
		FailureCodeMissingLeanCheckResult,
		FailureCodeLeanCheckFailed,
		FailureCodeLeanObligationMismatch,
		FailureCodeLeanReleaseIDMismatch,
		FailureCodeUnauthorizedLeanTheorem,
		ReasonRegistryAdmissionFailed,
		"PCS_MANIFEST_HASH_MISMATCH",
		"certificate_id_mismatch",
		"signed_input_bundle_hash_match",
	}
}

func failureCodesMatch(expected, observed []string) bool {
	if len(expected) == 0 {
		return true
	}
	for _, want := range expected {
		found := false
		for _, got := range observed {
			if want == got {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}

func outcomeMatchesExpect(expect, outcome string) bool {
	switch expect {
	case "admit":
		return outcome == "admit"
	case "reject":
		return outcome == "reject"
	default:
		return false
	}
}

func scoreLocalization(c AdmissionBenchmarkCase, rcvr ReleaseChainValidationResult) *FailureLocalizationCaseResult {
	loc := &FailureLocalizationCaseResult{CaseID: c.CaseID, ExpectedCheckID: c.Localization.CheckID}
	for _, chk := range rcvr.Checks {
		if chk.Status != "failed" {
			continue
		}
		if c.Localization.CheckID != "" && chk.CheckID != c.Localization.CheckID {
			continue
		}
		loc.ObservedCheckID = chk.CheckID
		if c.Localization.ArtifactPath != "" {
			if ap, ok := chk.Details["artifact_path"].(string); ok {
				loc.ArtifactPathMatch = strings.Contains(ap, c.Localization.ArtifactPath) || ap == c.Localization.ArtifactPath
			}
		} else {
			loc.ArtifactPathMatch = true
		}
		loc.Passed = loc.ObservedCheckID != "" && loc.ArtifactPathMatch
		return loc
	}
	loc.Passed = false
	return loc
}

func scoreExplainQuality(c AdmissionBenchmarkCase, rcvr ReleaseChainValidationResult) *ExplainQualityCaseScore {
	req := c.ExplainRequirements
	report := BuildExplainReleaseChainReport(rcvr)
	var target FailureExplanation
	wantCheck := ""
	if c.Localization != nil {
		wantCheck = c.Localization.CheckID
	}
	for _, fe := range report.Failed {
		if wantCheck != "" && fe.CheckID == wantCheck {
			target = fe
			break
		}
	}
	if target.CheckID == "" && len(report.Failed) > 0 {
		target = report.Failed[0]
	}
	fields := map[string]bool{}
	var score, total float64
	checkField := func(required bool, present bool, name string) {
		if !required {
			return
		}
		total++
		fields[name] = present
		if present {
			score++
		}
	}
	checkField(req.FailureCode, target.FailureCode != "", "failure_code")
	checkField(req.ArtifactPath, target.ArtifactPath != "", "artifact_path")
	checkField(req.Expected, target.Expected != "", "expected")
	checkField(req.Actual, target.Actual != "", "actual")
	checkField(req.ResponsibleComponent, target.ResponsibleComponent != "", "responsible_component")
	checkField(req.RepairHint, target.RepairHint != "", "repair_hint")
	checkField(req.RegistryCheckRef, target.RegistryCheckRef != "", "registry_check_ref")
	checkField(req.HandoffRef, target.HandoffRef != "", "handoff_ref")
	if req.FormalTheorem {
		combined := target.RepairHint + target.Actual + target.Expected
		checkField(true, strings.Contains(combined, "theorem") || strings.Contains(combined, "admissible_") || strings.Contains(combined, "witness"), "formal_theorem")
	}
	completeness := 1.0
	if total > 0 {
		completeness = score / total
	}
	return &ExplainQualityCaseScore{CaseID: c.CaseID, Completeness: completeness, Fields: fields}
}

func computeBenchmarkMetrics(results []AdmissionBenchmarkCaseResult, explain []ExplainQualityCaseScore) BenchmarkRunMetrics {
	var validTotal, validPass, invalidTotal, invalidPass int
	var locTotal, locPass, codeTotal, codePass int
	for _, r := range results {
		if r.Kind == "valid" {
			validTotal++
			if r.Passed {
				validPass++
			}
			continue
		}
		invalidTotal++
		if r.Passed {
			invalidPass++
		}
		if len(r.ExpectFailureCodes) > 0 {
			codeTotal++
			if r.FailureCodeMatch {
				codePass++
			}
			locTotal++
			if r.LocalizationMatch {
				locPass++
			}
		}
	}
	var explainSum float64
	for _, e := range explain {
		explainSum += e.Completeness
	}
	explainMean := 0.0
	if len(explain) > 0 {
		explainMean = explainSum / float64(len(explain))
	}
	return BenchmarkRunMetrics{
		ValidReleaseAdmissionRate:      rate(validPass, validTotal),
		InvalidReleaseRejectionRate:    rate(invalidPass, invalidTotal),
		FailureLocalizationAccuracy:    rate(locPass, locTotal),
		FailureCodeAccuracy:            rate(codePass, codeTotal),
		ExplainOutputCompleteness:      explainMean,
		RegistryCheckCoverage:          1.0,
		AdmissionProfileCoverage:       1.0,
		FormalCheckEnforcementCoverage: formalCheckEnforcementRate(results),
	}
}

func enrichBenchmarkMetrics(base BenchmarkRunMetrics, cov CoverageReportV0, results []AdmissionBenchmarkCaseResult) BenchmarkRunMetrics {
	base.RegistryCheckCoverage = registryCheckCoverage(cov)
	base.AdmissionProfileCoverage = admissionProfileCoverage(cov)
	base.FormalCheckEnforcementCoverage = formalCheckEnforcementRate(results)
	return base
}

func registrySemanticCheckMatched(required, observed string) bool {
	if required == "" || observed == "" {
		return false
	}
	if required == observed {
		return true
	}
	return strings.HasSuffix(observed, "."+required)
}

func registryCheckCoverage(cov CoverageReportV0) float64 {
	required := cov.Admission.RegistryChecksRequired
	if len(required) == 0 {
		return 1.0
	}
	matched := 0
	for _, req := range required {
		for _, obs := range cov.Admission.RegistryChecksObserved {
			if registrySemanticCheckMatched(req, obs) {
				matched++
				break
			}
		}
	}
	return rate(matched, len(required))
}

func admissionProfileCoverage(cov CoverageReportV0) float64 {
	if len(cov.Admission.ProfilesExercised) == 0 {
		return 0.0
	}
	if len(cov.Admission.RegistryChecksRequired) == 0 {
		return 1.0
	}
	return registryCheckCoverage(cov)
}

func formalCheckEnforcementRate(results []AdmissionBenchmarkCaseResult) float64 {
	var total, pass int
	for _, r := range results {
		if r.Kind != "invalid" || !expectsFormalFailure(r.ExpectFailureCodes) {
			continue
		}
		total++
		if r.Passed {
			pass++
		}
	}
	return rate(pass, total)
}

func expectsReleaseAdmissionFailure(c AdmissionBenchmarkCase) bool {
	for _, code := range c.ExpectFailureCodes {
		switch code {
		case FailureCodeReleaseModeHandoffRequired,
			FailureCodeReleaseModeRegistryRequired,
			FailureCodeReleaseModeManifestRequired,
			FailureCodeLegacyHandoffForbiddenInReleaseMode,
			FailureCodeMissingAdmissionProfile,
			FailureCodeUnknownAdmissionProfile:
			return true
		}
	}
	return false
}

func expectsFormalFailure(codes []string) bool {
	for _, code := range codes {
		switch code {
		case FailureCodeMissingLeanCheckResult, FailureCodeLeanCheckFailed, FailureCodeLeanReleaseIDMismatch,
			FailureCodeUnauthorizedLeanTheorem, "missing_proof_obligation":
			return true
		}
	}
	return false
}

func rate(pass, total int) float64 {
	if total == 0 {
		return 1.0
	}
	return float64(pass) / float64(total)
}

func buildCoverageReport(runID string, workflow AdmissionBenchmarkWorkflow, profile *AdmissionProfile, rcvr *ReleaseChainValidationResult) CoverageReportV0 {
	cov := CoverageReportV0{
		SchemaVersion: SchemaVersionV0,
		RunID:         runID,
		Workflow:      workflow.WorkflowID,
		Admission: AdmissionCoverage{
			ProfilesExercised:      []string{workflow.ProfileID},
			RegistryChecksRequired: []string{},
			RegistryChecksObserved: []string{},
		},
		Formal: FormalCoverage{
			ObligationKindsChecked: []string{},
			FormalCheckIDsObserved: []string{},
		},
	}
	if profile != nil {
		cov.Admission.RegistryChecksRequired = append([]string(nil), profile.RequiredRegistryChecks...)
	}
	if profile != nil && profile.FormalChecks != nil {
		cov.Formal.FormalChecksRequired = profile.FormalChecks.Required
		cov.Formal.ObligationKindsChecked = append([]string(nil), profile.FormalChecks.RequiredObligations...)
	}
	if rcvr == nil {
		return cov
	}
	for _, c := range rcvr.Checks {
		if strings.HasPrefix(c.CheckID, "formal.") {
			cov.Formal.FormalCheckIDsObserved = append(cov.Formal.FormalCheckIDsObserved, c.CheckID)
		}
		if strings.HasPrefix(c.CheckID, "registry.") {
			exec, _ := c.Details["execution"].(string)
			switch exec {
			case RegistryExecutionPassed, RegistryExecutionFailed:
				cov.Registry.SemanticChecksExecuted++
			case RegistryExecutionDeferred:
				cov.Registry.SemanticChecksDeferred++
			case RegistryExecutionSkippedNonRelease:
				cov.Registry.SemanticChecksSkipped++
			}
			cov.Admission.RegistryChecksObserved = append(cov.Admission.RegistryChecksObserved, c.CheckID)
			if semantic, ok := c.Details["semantic_check_id"].(string); ok && semantic != "" {
				cov.Admission.RegistryChecksObserved = append(cov.Admission.RegistryChecksObserved, semantic)
			}
		}
		switch c.CheckID {
		case "registry_artifact_registered":
			if c.Status == "passed" {
				cov.Registry.RegisteredArtifactsChecked++
			}
		case "registry_required_fields_present":
			if c.Status == "passed" {
				cov.Registry.RequiredFieldsChecked++
			}
		case "registry_status_allowed":
			if c.Status == "passed" {
				cov.Registry.AllowedStatusesChecked++
			}
		}
		if c.Status == "passed" {
			cov.Registry.ReleaseBlockingPassed++
		}
		if c.Status == "failed" {
			cov.Registry.ReleaseBlockingFailed++
		}
	}
	cov.Admission.RegistryChecksObserved = uniqueStrings(cov.Admission.RegistryChecksObserved)
	cov.Formal.FormalCheckIDsObserved = uniqueStrings(cov.Formal.FormalCheckIDsObserved)
	sort.Strings(cov.Admission.RegistryChecksObserved)
	sort.Strings(cov.Formal.FormalCheckIDsObserved)
	return cov
}

