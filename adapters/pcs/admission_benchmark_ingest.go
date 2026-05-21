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

// PCSBenchIngestLogs lists log paths relative to bundle_dir.
type PCSBenchIngestLogs struct {
	RunLog   string            `json:"run_log"`
	CaseLogs map[string]string `json:"case_logs,omitempty"`
}

// PCSBenchIngestV0 is the single-file manifest pcs-bench reads when importing PF outputs.
type PCSBenchIngestV0 struct {
	SchemaVersion              string                           `json:"schema_version"`
	IngestID                   string                           `json:"ingest_id"`
	BundleDir                  string                           `json:"bundle_dir"`
	BenchmarkReport            PCSBenchmarkReport               `json:"benchmark_report"`
	BenchmarkRuns              []PCSBenchmarkRun                `json:"benchmark_runs"`
	CoverageReports            []PCSCoverageReport              `json:"coverage_reports"`
	ExplainQualityReports      []PCSExplainQualityReport        `json:"explain_quality_reports"`
	FailureLocalizationReports []PCSFailureLocalizationResult   `json:"failure_localization_reports"`
	Commands                   []PCSBenchmarkCommandEntry       `json:"commands"`
	Logs                       PCSBenchIngestLogs               `json:"logs"`
	SourceRepo                 string                           `json:"source_repo,omitempty"`
	SourceCommit               string                           `json:"source_commit,omitempty"`
	SignatureOrDigest          string                           `json:"signature_or_digest,omitempty"`
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

func buildPCSBenchIngest(bundle PCSBenchmarkBundle, bundleDir string, executions []benchmarkCaseExecution) PCSBenchIngestV0 {
	coverage := make([]PCSCoverageReport, 0, len(bundle.CoverageByMetric))
	for _, m := range []string{"registry_coverage", "formal_check_coverage", "admission_profile_coverage", "release_reproducibility", "failure_localization", "certificate_completeness"} {
		if c, ok := bundle.CoverageByMetric[m]; ok {
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
	caseLogs := map[string]string{}
	for _, ex := range executions {
		caseLogs[ex.Case.CaseID] = filepath.Join("logs", ex.Case.CaseID+".log")
	}
	ingestID := bundle.Report.ReportID
	if ingestID == "" {
		ingestID = "pcs-bench-ingest-" + bundle.Report.BenchmarkSuiteID
	}
	sum := sha256.Sum256([]byte(ingestID + bundleDir + bundle.Report.SignatureOrDigest))
	return PCSBenchIngestV0{
		SchemaVersion:              SchemaVersionV0,
		IngestID:                   ingestID,
		BundleDir:                  ".",
		BenchmarkReport:            bundle.Report,
		BenchmarkRuns:              runs,
		CoverageReports:            coverage,
		ExplainQualityReports:      explains,
		FailureLocalizationReports: flrs,
		Commands:                   commands,
		Logs: PCSBenchIngestLogs{
			RunLog:   "logs/run.log",
			CaseLogs: caseLogs,
		},
		SourceRepo:        VerifierSourceRepo,
		SourceCommit:      bundle.Report.SourceCommit,
		SignatureOrDigest: "sha256:" + hex.EncodeToString(sum[:]),
	}
}

func writePCSBenchIngest(repoRoot, pcsCoreRoot, dir string, ingest PCSBenchIngestV0) error {
	doc := mustJSONDoc(ingest)
	if err := ValidateDocumentAgainstSchemaPreferPCSCore(pcsCoreRoot, repoRoot, "PCSBenchIngest.v0.schema.json", doc); err != nil {
		return fmt.Errorf("validate pcs_bench_ingest.v0.json: %w", err)
	}
	data, err := json.MarshalIndent(ingest, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(filepath.Join(dir, "pcs_bench_ingest.v0.json"), data, 0644)
}

// ValidatePCSBenchIngest validates pcs_bench_ingest.v0.json.
func ValidatePCSBenchIngest(repoRoot string, ingest PCSBenchIngestV0) error {
	return validateBenchmarkDoc(repoRoot, "PCSBenchIngest.v0.schema.json", ingest)
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
		return "PCSBenchIngest.v0.schema.json", nil
	default:
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
