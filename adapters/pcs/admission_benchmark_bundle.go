// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
)

// RequiredAdmissionInvalidCaseIDs are canonical negative cases PCS admission must exercise (labtrust suite).
var RequiredAdmissionInvalidCaseIDs = []string{
	"missing_handoff",
	"legacy_handoff_in_release_mode",
	"missing_registry",
	"wrong_admission_profile",
	"rejected_certificate",
	"trace_hash_mismatch",
	"bundle_hash_mismatch",
	"registry_wrong_producer",
	"registry_disallowed_status",
	"missing_proof_obligation",
	"missing_lean_check_result",
	"failed_lean_check",
	"unauthorized_lean_theorem",
	"result_hash_mismatch",
	"missing_code_commit",
	"nonzero_exit_code",
}

// writeAdmissionBenchmarkBundle emits a pcs-core benchmark bundle for pcs-bench ingestion.
func writeAdmissionBenchmarkBundle(repoRoot, dir string, bundle PCSBenchmarkBundle, executions []benchmarkCaseExecution) error {
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	logsDir := filepath.Join(dir, "logs")
	if err := os.MkdirAll(logsDir, 0755); err != nil {
		return err
	}
	runsDir := filepath.Join(dir, "runs")
	if err := os.MkdirAll(runsDir, 0755); err != nil {
		return err
	}

	validateDoc := func(schema string, v any) error {
		if repoRoot == "" || schema == "" {
			return nil
		}
		return ValidateDocumentAgainstSchema(repoRoot, schema, mustJSONDoc(v))
	}
	writeDoc := func(path, schema string, v any) error {
		if err := validateDoc(schema, v); err != nil {
			return fmt.Errorf("validate %s: %w", filepath.Base(path), err)
		}
		data, err := json.MarshalIndent(v, "", "  ")
		if err != nil {
			return err
		}
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			return err
		}
		return os.WriteFile(path, data, 0644)
	}

	if err := writeDoc(filepath.Join(dir, "benchmark_report.v0.json"), "BenchmarkReport.v0.schema.json", bundle.Report); err != nil {
		return err
	}
	for _, run := range bundle.Runs {
		if err := validateDoc("BenchmarkRun.v0.schema.json", run); err != nil {
			return fmt.Errorf("validate benchmark run %s: %w", run.CaseID, err)
		}
	}
	runData, err := json.MarshalIndent(bundle.Runs, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "benchmark_run.v0.json"), runData, 0644); err != nil {
		return err
	}
	for _, flr := range bundle.FailureLocalizations {
		if err := validateDoc("FailureLocalizationResult.v0.schema.json", flr); err != nil {
			return fmt.Errorf("validate failure localization %s: %w", flr.CaseID, err)
		}
	}
	flrs := bundle.FailureLocalizations
	if flrs == nil {
		flrs = []PCSFailureLocalizationResult{}
	}
	flrData, err := json.MarshalIndent(flrs, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "failure_localization_result.v0.json"), flrData, 0644); err != nil {
		return err
	}
	coverageList := make([]PCSCoverageReport, 0, len(bundle.CoverageByMetric))
	for _, m := range []string{"registry_coverage", "formal_check_coverage", "release_reproducibility", "failure_localization", "certificate_completeness"} {
		if c, ok := bundle.CoverageByMetric[m]; ok {
			if err := validateDoc("CoverageReport.v0.schema.json", c); err != nil {
				return fmt.Errorf("validate coverage %s: %w", m, err)
			}
			coverageList = append(coverageList, c)
		}
	}
	covData, err := json.MarshalIndent(coverageList, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "coverage_report.v0.json"), covData, 0644); err != nil {
		return err
	}
	for _, eq := range bundle.ExplainQuality {
		if err := validateDoc("ExplainQualityReport.v0.schema.json", eq); err != nil {
			return fmt.Errorf("validate explain quality %s: %w", eq.CaseID, err)
		}
	}
	explains := bundle.ExplainQuality
	if explains == nil {
		explains = []PCSExplainQualityReport{}
	}
	eqData, err := json.MarshalIndent(explains, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "explain_quality_report.v0.json"), eqData, 0644); err != nil {
		return err
	}

	cmdData, err := json.MarshalIndent(bundle.Commands, "", "  ")
	if err != nil {
		return err
	}
	if err := os.WriteFile(filepath.Join(dir, "commands.json"), cmdData, 0644); err != nil {
		return err
	}

	explainByCase := map[string]PCSExplainQualityReport{}
	for _, eq := range bundle.ExplainQuality {
		explainByCase[eq.CaseID] = eq
	}
	flrByCase := map[string]PCSFailureLocalizationResult{}
	for _, flr := range bundle.FailureLocalizations {
		flrByCase[flr.CaseID] = flr
	}
	logsByCase := map[string][]string{}
	for _, ex := range executions {
		logsByCase[ex.Case.CaseID] = append(logsByCase[ex.Case.CaseID], ex.LogLines...)
	}
	var logLines []string
	for _, ex := range bundle.Runs {
		caseID := ex.CaseID
		caseDir := filepath.Join(runsDir, caseID)
		if err := writeDoc(filepath.Join(caseDir, "benchmark_run.v0.json"), "BenchmarkRun.v0.schema.json", ex); err != nil {
			return err
		}
		if eq, ok := explainByCase[caseID]; ok {
			if err := writeDoc(filepath.Join(caseDir, "explain_quality_report.v0.json"), "ExplainQualityReport.v0.schema.json", eq); err != nil {
				return err
			}
		}
		if flr, ok := flrByCase[caseID]; ok {
			if err := writeDoc(filepath.Join(caseDir, "failure_localization_result.v0.json"), "FailureLocalizationResult.v0.schema.json", flr); err != nil {
				return err
			}
		}
		caseLog := strings.Join(logsByCase[caseID], "\n")
		if caseLog == "" {
			caseLog = fmt.Sprintf("case=%s status=%s failure=%s", caseID, ex.ObservedStatus, ex.ObservedFailureCode)
		}
		if err := os.WriteFile(filepath.Join(caseDir, "run.log"), []byte(caseLog+"\n"), 0644); err != nil {
			return err
		}
		if err := os.WriteFile(filepath.Join(logsDir, caseID+".log"), []byte(caseLog+"\n"), 0644); err != nil {
			return err
		}
		logLines = append(logLines, caseLog)
	}
	if err := os.WriteFile(filepath.Join(logsDir, "run.log"), []byte(strings.Join(logLines, "\n")+"\n"), 0644); err != nil {
		return err
	}

	ingest := buildPCSBenchIngest(bundle, dir, executions)
	if err := writePCSBenchIngest(repoRoot, dir, ingest); err != nil {
		return err
	}

	// PF-internal suite summary for backward-compatible tooling.
	if bundle.InternalSuite.RunID != "" {
		suitePath := filepath.Join(dir, "admission_benchmark_suite.v0.json")
		data, err := json.MarshalIndent(bundle.InternalSuite, "", "  ")
		if err != nil {
			return err
		}
		if err := os.WriteFile(suitePath, data, 0644); err != nil {
			return err
		}
	}
	return nil
}

func mustJSONDoc(v any) any {
	raw, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	var doc any
	if err := json.Unmarshal(raw, &doc); err != nil {
		panic(err)
	}
	return doc
}

// FormatBenchmarkAdmissionSummaryJSON returns a compact JSON summary for --json-summary.
func FormatBenchmarkAdmissionSummaryJSON(run AdmissionBenchmarkSuiteV0, outDir string) (string, error) {
	summary := map[string]any{
		"run_id":                            run.RunID,
		"workflow":                          run.Workflow,
		"profile_id":                        run.ProfileID,
		"started_at":                        run.StartedAt,
		"completed_at":                      run.CompletedAt,
		"out_dir":                           outDir,
		"metrics":                           run.Metrics,
		"total_cases":                       len(run.Cases),
		"passed_cases":                      0,
		"failed_cases":                      0,
	}
	for _, c := range run.Cases {
		if c.Passed {
			summary["passed_cases"] = summary["passed_cases"].(int) + 1
		} else {
			summary["failed_cases"] = summary["failed_cases"].(int) + 1
		}
	}
	raw, err := json.MarshalIndent(summary, "", "  ")
	if err != nil {
		return "", err
	}
	return string(raw) + "\n", nil
}

// ValidateAdmissionBenchmarkBundleDir validates a written pcs-core benchmark bundle (pcs-bench ingestion gate).
func ValidateAdmissionBenchmarkBundleDir(repoRoot, dir string) error {
	if repoRoot == "" {
		var err error
		repoRoot, err = FindRepoRoot(dir)
		if err != nil {
			return err
		}
	}
	required := []string{
		"benchmark_report.v0.json",
		"benchmark_run.v0.json",
		"failure_localization_result.v0.json",
		"coverage_report.v0.json",
		"explain_quality_report.v0.json",
		"pcs_bench_ingest.v0.json",
		"commands.json",
		filepath.Join("logs", "run.log"),
	}
	for _, name := range required {
		if _, err := os.Stat(filepath.Join(dir, name)); err != nil {
			return fmt.Errorf("bundle missing %s: %w", name, err)
		}
	}
	validateArray := func(path, schema string) error {
		data, err := os.ReadFile(path)
		if err != nil {
			return err
		}
		var doc any
		if err := json.Unmarshal(data, &doc); err != nil {
			return err
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
	reportPath := filepath.Join(dir, "benchmark_report.v0.json")
	reportData, err := os.ReadFile(reportPath)
	if err != nil {
		return err
	}
	var report PCSBenchmarkReport
	if err := json.Unmarshal(reportData, &report); err != nil {
		return err
	}
	if err := ValidatePCSBenchmarkReport(repoRoot, report); err != nil {
		return err
	}
	if err := validateArray(filepath.Join(dir, "benchmark_run.v0.json"), "BenchmarkRun.v0.schema.json"); err != nil {
		return err
	}
	if err := validateArray(filepath.Join(dir, "failure_localization_result.v0.json"), "FailureLocalizationResult.v0.schema.json"); err != nil {
		return err
	}
	if err := validateArray(filepath.Join(dir, "coverage_report.v0.json"), "CoverageReport.v0.schema.json"); err != nil {
		return err
	}
	if err := validateArray(filepath.Join(dir, "explain_quality_report.v0.json"), "ExplainQualityReport.v0.schema.json"); err != nil {
		return err
	}
	for _, ref := range report.Runs {
		runPath := filepath.Join(dir, ref.Path)
		if _, err := os.Stat(runPath); err != nil {
			return fmt.Errorf("benchmark report references missing run artifact %s: %w", ref.Path, err)
		}
	}
	ingestPath := filepath.Join(dir, "pcs_bench_ingest.v0.json")
	ingestData, err := os.ReadFile(ingestPath)
	if err != nil {
		return err
	}
	var ingest PCSBenchIngestV0
	if err := json.Unmarshal(ingestData, &ingest); err != nil {
		return err
	}
	if err := ValidatePCSBenchIngest(repoRoot, ingest); err != nil {
		return err
	}
	if ingest.BenchmarkReport.ReportID != report.ReportID {
		return fmt.Errorf("pcs_bench_ingest benchmark_report.report_id mismatch")
	}
	return nil
}
