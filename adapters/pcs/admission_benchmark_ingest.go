// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// CanonicalExplainQualitySections are required pcs-core ExplainQualityReport.v0 sections for PF admission.
var CanonicalExplainQualitySections = []string{
	"provenance",
	"hashes",
	"handoffs",
	"verification",
	"formal_checks",
	"limitations",
	"lineage",
	"repair_hints",
}

// PCSBenchmarkArtifactRef matches pcs-core BenchmarkArtifactRef.v0.
type PCSBenchmarkArtifactRef struct {
	SchemaVersion     string `json:"schema_version"`
	ArtifactType      string `json:"artifact_type"`
	Path              string `json:"path"`
	SHA256            string `json:"sha256"`
	Role              string `json:"role"`
	SourceRepo        string `json:"source_repo"`
	SourceCommit      string `json:"source_commit"`
	SignatureOrDigest string `json:"signature_or_digest"`
}

// PCSProfileCoverageReport matches pcs-core ProfileCoverageReport.v0.
type PCSProfileCoverageReport struct {
	SchemaVersion           string         `json:"schema_version"`
	CoverageID              string         `json:"coverage_id"`
	WorkflowProfileID       string         `json:"workflow_profile_id"`
	ProducerID              string         `json:"producer_id"`
	SuiteID                 string         `json:"suite_id,omitempty"`
	ArtifactTypesRequired   []string       `json:"artifact_types_required"`
	ArtifactTypesCovered    []string       `json:"artifact_types_covered"`
	SemanticChecksRequired  []string       `json:"semantic_checks_required"`
	SemanticChecksCovered   []string       `json:"semantic_checks_covered"`
	HandoffStepsRequired    []string       `json:"handoff_steps_required"`
	HandoffStepsCovered     []string       `json:"handoff_steps_covered"`
	Numerator               float64        `json:"numerator"`
	Denominator             float64        `json:"denominator"`
	CoverageRatio           float64        `json:"coverage_ratio"`
	Details                 map[string]any `json:"details"`
	SourceRepo              string         `json:"source_repo"`
	SourceCommit            string         `json:"source_commit"`
	SignatureOrDigest       string         `json:"signature_or_digest"`
}

// PCSBenchIngestV0 is the pcs-core PcsBenchIngest.v0 manifest for pcs-bench ingestion.
type PCSBenchIngestV0 struct {
	SchemaVersion              string                     `json:"schema_version"`
	ProducerID                 string                     `json:"producer_id"`
	SuiteID                    string                     `json:"suite_id"`
	WorkflowID                 string                     `json:"workflow_id"`
	BenchmarkRuns              []PCSBenchmarkRun          `json:"benchmark_runs"`
	CoverageReports            []PCSCoverageReport        `json:"coverage_reports"`
	ExplainQualityReports      []PCSExplainQualityReport  `json:"explain_quality_reports"`
	FailureLocalizationReports []PCSFailureLocalizationResult `json:"failure_localization_reports"`
	ProfileCoverageReports     []PCSProfileCoverageReport `json:"profile_coverage_reports"`
	Commands                   []PCSBenchmarkCommandEntry `json:"commands"`
	Logs                       []string                   `json:"logs"`
	ArtifactRefs               []PCSBenchmarkArtifactRef  `json:"artifact_refs,omitempty"`
	SourceRepo                 string                     `json:"source_repo"`
	SourceCommit               string                     `json:"source_commit"`
	SignatureOrDigest          string                     `json:"signature_or_digest"`
}

// ExportPCSExplainQualityCaseInput carries per-case state for pcs-core ExplainQualityReport.v0 export.
type ExportPCSExplainQualityCaseInput struct {
	Case         AdmissionBenchmarkCase
	Result       AdmissionBenchmarkCaseResult
	RCVR         *ReleaseChainValidationResult
	VR           *VerificationResult
	SuiteID      string
	WorkflowID   string
	SourceCommit string
}

// ExportPCSExplainQualityReport maps PF explain requirements to pcs-core ExplainQualityReport.v0 sections.
func ExportPCSExplainQualityReport(in ExportPCSExplainQualityCaseInput) *PCSExplainQualityReport {
	return buildPCSExplainQualityReport(
		in.Case,
		in.Result,
		in.RCVR,
		in.VR,
		in.SourceCommit,
		in.SuiteID,
		in.WorkflowID,
	)
}

func benchmarkBundleRelPath(elem ...string) string {
	return filepath.ToSlash(filepath.Join(elem...))
}

func buildPCSBenchmarkArtifactRef(artifactType, relPath, contentDigest, sourceCommit string) PCSBenchmarkArtifactRef {
	relPath = benchmarkBundleRelPath(relPath)
	refID := fmt.Sprintf("ref-%s-%s", artifactType, filepath.Base(relPath))
	return PCSBenchmarkArtifactRef{
		SchemaVersion:     SchemaVersionV0,
		ArtifactType:      artifactType,
		Path:              relPath,
		SHA256:            contentDigest,
		Role:              "producer_export",
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestBenchmarkRun(refID, artifactType, relPath, "ref", contentDigest),
	}
}

func buildPCSProfileCoverageReport(
	workflow AdmissionBenchmarkWorkflow,
	profile *AdmissionProfile,
	cov CoverageReportV0,
	suiteID, sourceCommit string,
	ratio float64,
) PCSProfileCoverageReport {
	requiredArtifacts := []string{}
	coveredArtifacts := []string{}
	requiredHandoffs := []string{}
	coveredHandoffs := []string{}
	if profile != nil {
		for _, k := range profile.RequiredHandoffKinds {
			requiredHandoffs = append(requiredHandoffs, string(k))
		}
	}
	if profile != nil && len(profile.RequiredHandoffKinds) > 0 {
		coveredHandoffs = append(coveredHandoffs, requiredHandoffs...)
	}
	requiredChecks := cov.Admission.RegistryChecksRequired
	if requiredChecks == nil {
		requiredChecks = []string{}
	}
	coveredChecks := cov.Admission.RegistryChecksObserved
	if coveredChecks == nil {
		coveredChecks = []string{}
	}
	numerator := float64(len(coveredChecks) + len(coveredArtifacts) + len(coveredHandoffs))
	denominator := float64(len(requiredChecks) + len(requiredArtifacts) + len(requiredHandoffs))
	if denominator < 1 {
		denominator = 1
	}
	if ratio <= 0 {
		ratio = numerator / denominator
	}
	if ratio > 1 {
		ratio = 1
	}
	return PCSProfileCoverageReport{
		SchemaVersion:          SchemaVersionV0,
		CoverageID:             suiteID + "-profile-coverage",
		WorkflowProfileID:      workflow.ProfileID,
		ProducerID:             "provability-fabric",
		SuiteID:                suiteID,
		ArtifactTypesRequired:  requiredArtifacts,
		ArtifactTypesCovered:   coveredArtifacts,
		SemanticChecksRequired: requiredChecks,
		SemanticChecksCovered:  coveredChecks,
		HandoffStepsRequired:   requiredHandoffs,
		HandoffStepsCovered:    coveredHandoffs,
		Numerator:              numerator,
		Denominator:            denominator,
		CoverageRatio:          ratio,
		Details: map[string]any{
			"profiles_exercised": cov.Admission.ProfilesExercised,
			"workflow_id":        pcsBenchmarkWorkflowID(workflow.WorkflowID),
		},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      sourceCommit,
		SignatureOrDigest: digestCoverage(suiteID, "profile_coverage", ratio),
	}
}

func buildPCSBenchIngest(
	bundle PCSBenchmarkBundle,
	workflow AdmissionBenchmarkWorkflow,
	profile *AdmissionProfile,
	covReport CoverageReportV0,
	bundleDir string,
	executions []benchmarkCaseExecution,
) PCSBenchIngestV0 {
	coverage := make([]PCSCoverageReport, 0, len(bundle.CoverageByMetric))
	for _, key := range []string{"registry_coverage", "formal_check_coverage", "admission_profile_coverage", "release_reproducibility"} {
		if c, ok := bundle.CoverageByMetric[key]; ok {
			coverage = append(coverage, c)
		}
	}
	runs := bundle.Runs
	if runs == nil {
		runs = []PCSBenchmarkRun{}
	}
	explains := bundle.ExplainQuality
	if explains == nil {
		explains = []PCSExplainQualityReport{}
	}
	flrs := bundle.FailureLocalizations
	if flrs == nil {
		flrs = []PCSFailureLocalizationResult{}
	}
	commands := bundle.Commands
	if commands == nil {
		commands = []PCSBenchmarkCommandEntry{}
	}
	logLines := []string{}
	for _, ex := range executions {
		line := strings.Join(ex.LogLines, "\n")
		if line == "" {
			line = fmt.Sprintf("case=%s outcome=%s passed=%v", ex.Case.CaseID, ex.Result.Outcome, ex.Result.Passed)
		}
		logLines = append(logLines, line)
	}
	profileCov := buildPCSProfileCoverageReport(
		workflow,
		profile,
		covReport,
		suiteIDFromWorkflow(workflow.WorkflowID),
		bundle.Report.SourceCommit,
		bundle.Report.Summary.RegistryCoverage,
	)
	refs := buildPCSBenchIngestArtifactRefs(bundleDir, runs, coverage, explains, profileCov, flrs)
	ingest := PCSBenchIngestV0{
		SchemaVersion:              SchemaVersionV0,
		ProducerID:                 "provability-fabric",
		SuiteID:                    bundle.Report.BenchmarkSuiteID,
		WorkflowID:                 pcsBenchmarkWorkflowID(workflow.WorkflowID),
		BenchmarkRuns:              runs,
		CoverageReports:            coverage,
		ExplainQualityReports:      explains,
		FailureLocalizationReports: flrs,
		ProfileCoverageReports:     []PCSProfileCoverageReport{profileCov},
		Commands:                   commands,
		Logs:                       logLines,
		ArtifactRefs:               refs,
		SourceRepo:                 VerifierSourceRepo,
		SourceCommit:               bundle.Report.SourceCommit,
	}
	ingest.SignatureOrDigest = digestPCSBenchIngest(ingest)
	return ingest
}

func digestPCSBenchIngest(ingest PCSBenchIngestV0) string {
	copy := ingest
	copy.SignatureOrDigest = ""
	raw, err := json.Marshal(copy)
	if err != nil {
		sum := sha256.Sum256([]byte(ingest.SuiteID + ingest.WorkflowID))
		return "sha256:" + hex.EncodeToString(sum[:])
	}
	sum := sha256.Sum256(raw)
	return "sha256:" + hex.EncodeToString(sum[:])
}

func coverageReportExportPath(metric, metricID string) string {
	switch metric {
	case "registry_coverage":
		return "coverage/registry_coverage_report.v0.json"
	case "formal_check_coverage":
		return "coverage/formal_check_coverage_report.v0.json"
	case "cross_domain_portability":
		return "coverage/admission_profile_coverage_report.v0.json"
	case "release_reproducibility":
		return "coverage/release_reproducibility_coverage_report.v0.json"
	}
	switch metricID {
	case "registry_coverage_score":
		return "coverage/registry_coverage_report.v0.json"
	case "formal_check_coverage_score":
		return "coverage/formal_check_coverage_report.v0.json"
	case "cross_domain_portability_score":
		return "coverage/admission_profile_coverage_report.v0.json"
	case "release_reproducibility_score":
		return "coverage/release_reproducibility_coverage_report.v0.json"
	default:
		return ""
	}
}

func buildPCSBenchIngestArtifactRefs(
	bundleDir string,
	runs []PCSBenchmarkRun,
	coverage []PCSCoverageReport,
	explains []PCSExplainQualityReport,
	profileCov PCSProfileCoverageReport,
	flrs []PCSFailureLocalizationResult,
) []PCSBenchmarkArtifactRef {
	refs := []PCSBenchmarkArtifactRef{}
	for _, run := range runs {
		if run.SignatureOrDigest == "" {
			continue
		}
		rel := benchmarkBundleRelPath("runs", run.CaseID, "benchmark_run.v0.json")
		if _, err := os.Stat(filepath.Join(bundleDir, rel)); err != nil {
			continue
		}
		refs = append(refs, buildPCSBenchmarkArtifactRef(
			"BenchmarkRun.v0", rel, run.SignatureOrDigest, run.SourceCommit,
		))
	}
	for _, cov := range coverage {
		rel := coverageReportExportPath(cov.Metric, cov.MetricID)
		if rel == "" || cov.SignatureOrDigest == "" {
			continue
		}
		if _, err := os.Stat(filepath.Join(bundleDir, rel)); err != nil {
			continue
		}
		refs = append(refs, buildPCSBenchmarkArtifactRef(
			"CoverageReport.v0", rel, cov.SignatureOrDigest, cov.SourceCommit,
		))
	}
	profilePath := "coverage/admission_profile.profile_coverage_report.v0.json"
	if profileCov.SignatureOrDigest != "" {
		if _, err := os.Stat(filepath.Join(bundleDir, profilePath)); err == nil {
			refs = append(refs, buildPCSBenchmarkArtifactRef(
				"ProfileCoverageReport.v0", profilePath, profileCov.SignatureOrDigest, profileCov.SourceCommit,
			))
		}
	}
	for _, eq := range explains {
		rel := benchmarkBundleRelPath("explain_quality", eq.CaseID+".explain_quality_report.v0.json")
		refs = append(refs, buildPCSBenchmarkArtifactRef(
			"ExplainQualityReport.v0", rel, eq.SignatureOrDigest, eq.SourceCommit,
		))
	}
	for _, flr := range flrs {
		rel := benchmarkBundleRelPath("failure_localization", flr.CaseID+".failure_localization_result.v0.json")
		refs = append(refs, buildPCSBenchmarkArtifactRef(
			"FailureLocalizationResult.v0", rel, flr.SignatureOrDigest, flr.SourceCommit,
		))
	}
	return refs
}

func writePCSBenchIngest(repoRoot, pcsCoreRoot, dir string, ingest PCSBenchIngestV0) error {
	if err := ValidatePCSBenchIngestSemantics(ingest); err != nil {
		return fmt.Errorf("pcs_bench_ingest semantics: %w", err)
	}
	doc := mustJSONDoc(ingest)
	if err := ValidateDocumentAgainstSchemaPreferPCSCore(pcsCoreRoot, repoRoot, "PcsBenchIngest.v0.schema.json", doc); err != nil {
		if err2 := ValidateDocumentAgainstSchemaPreferPCSCore(pcsCoreRoot, repoRoot, "PCSBenchIngest.v0.schema.json", doc); err2 != nil {
			return fmt.Errorf("validate pcs_bench_ingest.v0.json: %w", err)
		}
	}
	data, err := json.MarshalIndent(ingest, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(dir, "pcs_bench_ingest.v0.json"), data, 0644)
}

// ValidatePCSBenchIngest validates pcs_bench_ingest.v0.json.
func ValidatePCSBenchIngest(repoRoot string, ingest PCSBenchIngestV0) error {
	doc := mustJSONDoc(ingest)
	if err := validateBenchmarkDoc(repoRoot, "PcsBenchIngest.v0.schema.json", doc); err != nil {
		return validateBenchmarkDoc(repoRoot, "PCSBenchIngest.v0.schema.json", doc)
	}
	return nil
}

// BenchmarkArtifactSchemaForFile returns the pcs-core schema file for a benchmark bundle artifact path.
func BenchmarkArtifactSchemaForFile(name string) (string, error) {
	base := filepath.Base(name)
	switch base {
	case "benchmark_report.v0.json":
		return "BenchmarkReport.v0.schema.json", nil
	case "benchmark_run.v0.json":
		return "BenchmarkRun.v0.schema.json", nil
	case "coverage_report.v0.json":
		return "CoverageReport.v0.schema.json", nil
	case "explain_quality_report.v0.json":
		return "ExplainQualityReport.v0.schema.json", nil
	case "failure_localization_result.v0.json":
		return "FailureLocalizationResult.v0.schema.json", nil
	case "pcs_bench_ingest.v0.json":
		return "PcsBenchIngest.v0.schema.json", nil
	default:
		if strings.HasSuffix(base, ".pcs_bench_ingest.reference.json") {
			return "PcsBenchIngest.v0.schema.json", nil
		}
		if strings.HasSuffix(base, "coverage_report.v0.json") {
			return "CoverageReport.v0.schema.json", nil
		}
		if strings.HasSuffix(base, "profile_coverage_report.v0.json") {
			return "ProfileCoverageReport.v0.schema.json", nil
		}
		return "", fmt.Errorf("unknown benchmark artifact %q", base)
	}
}

// ValidateBenchmarkArtifactFile validates one benchmark bundle JSON file (pcs validate compatible).
func ValidateBenchmarkArtifactFile(repoRoot, path string) error {
	if repoRoot == "" {
		var err error
		repoRoot, err = FindRepoRoot(path)
		if err != nil {
			return err
		}
	}
	schema, err := BenchmarkArtifactSchemaForFile(path)
	if err != nil {
		return err
	}
	data, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	var doc any
	if err := json.Unmarshal(data, &doc); err != nil {
		return fmt.Errorf("parse %s: %w", path, err)
	}
	arr, ok := doc.([]any)
	if !ok {
		return ValidateDocumentAgainstSchema(repoRoot, schema, doc)
	}
	for i, item := range arr {
		if err := ValidateDocumentAgainstSchema(repoRoot, schema, item); err != nil {
			return fmt.Errorf("%s[%d]: %w", filepath.Base(path), i, err)
		}
	}
	return nil
}

// LoadPCSBenchIngestFromDir reads pcs_bench_ingest.v0.json from a benchmark output directory.
func LoadPCSBenchIngestFromDir(dir string) (PCSBenchIngestV0, error) {
	path := filepath.Join(dir, "pcs_bench_ingest.v0.json")
	data, err := os.ReadFile(path)
	if err != nil {
		return PCSBenchIngestV0{}, err
	}
	var ingest PCSBenchIngestV0
	if err := json.Unmarshal(data, &ingest); err != nil {
		return PCSBenchIngestV0{}, err
	}
	return ingest, nil
}

// ValidateBenchmarkBundleArtifacts validates standard pcs-core benchmark JSON files (pcs validate compatible).
func ValidateBenchmarkBundleArtifacts(repoRoot, dir string) error {
	return ValidateBenchmarkBundleArtifactsWithPCSCore(repoRoot, "", dir)
}

// ValidateBenchmarkBundleArtifactsWithPCSCore validates bundle artifacts; when pcsCoreRoot is set, uses pcs-core/schemas.
func ValidateBenchmarkBundleArtifactsWithPCSCore(repoRoot, pcsCoreRoot, dir string) error {
	if strings.TrimSpace(pcsCoreRoot) != "" {
		return ValidateAdmissionBenchmarkBundlePCSCore(pcsCoreRoot, dir)
	}
	for _, name := range []string{
		"benchmark_report.v0.json",
		"coverage_report.v0.json",
		"explain_quality_report.v0.json",
		"pcs_bench_ingest.v0.json",
	} {
		if err := ValidateBenchmarkArtifactFile(repoRoot, filepath.Join(dir, name)); err != nil {
			return err
		}
	}
	return ValidateAdmissionBenchmarkBundleDir(repoRoot, dir)
}
