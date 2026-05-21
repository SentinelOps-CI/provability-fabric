// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestBenchmarkBundleValidatesAgainstPCSCore(t *testing.T) {
	root := repoRoot(t)
	pcsCore := pcsCoreRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              casesDir,
		RegistryPath:          reg,
		OutDir:                out,
		ValidatePCSCoreOutput: pcsCore,
		RequireAllCasesPass:   true,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateAdmissionBenchmarkBundlePCSCore(pcsCore, out); err != nil {
		t.Fatalf("pcs-core bundle validation: %v", err)
	}
}

func TestAdmissionBenchmarkOutputsMatchPCSSchema(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateAdmissionBenchmarkBundleDir(root, out); err != nil {
		t.Fatalf("bundle ingest validation: %v", err)
	}
	for _, name := range []string{
		"benchmark_report.v0.json",
		"benchmark_run.v0.json",
		"failure_localization_result.v0.json",
		"coverage_report.v0.json",
		"explain_quality_report.v0.json",
		"pcs_bench_ingest.v0.json",
		"commands.json",
	} {
		if _, err := os.Stat(filepath.Join(out, name)); err != nil {
			t.Fatalf("missing output %s: %v", name, err)
		}
	}
	if _, err := os.Stat(filepath.Join(out, "logs", "run.log")); err != nil {
		t.Fatalf("missing logs/run.log: %v", err)
	}

	validateFile := func(path, schema string) {
		t.Helper()
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		var doc any
		if err := json.Unmarshal(data, &doc); err != nil {
			t.Fatalf("parse %s: %v", path, err)
		}
		if err := pcs.ValidateDocumentAgainstSchema(root, schema, doc); err != nil {
			// Root aggregate files are JSON arrays of per-case pcs-core documents.
			arr, ok := doc.([]any)
			if !ok {
				t.Fatalf("schema %s for %s: %v", schema, path, err)
			}
			for i, item := range arr {
				if err := pcs.ValidateDocumentAgainstSchema(root, schema, item); err != nil {
					t.Fatalf("schema %s for %s[%d]: %v", schema, path, i, err)
				}
			}
		}
	}

	validateFile(filepath.Join(out, "benchmark_report.v0.json"), "BenchmarkReport.v0.schema.json")
	validateFile(filepath.Join(out, "benchmark_run.v0.json"), "BenchmarkRun.v0.schema.json")
	validateFile(filepath.Join(out, "failure_localization_result.v0.json"), "FailureLocalizationResult.v0.schema.json")
	validateFile(filepath.Join(out, "coverage_report.v0.json"), "CoverageReport.v0.schema.json")
	validateFile(filepath.Join(out, "explain_quality_report.v0.json"), "ExplainQualityReport.v0.schema.json")
	validateFile(filepath.Join(out, "pcs_bench_ingest.v0.json"), "PcsBenchIngest.v0.schema.json")
}

func TestExportPCSExplainQualityReportTraceHashMismatch(t *testing.T) {
	root := repoRoot(t)
	c := pcs.AdmissionBenchmarkCase{
		CaseID:             "trace_hash_mismatch",
		Kind:               "invalid",
		ExpectFailureCodes: []string{pcs.ReasonTraceHashMismatch},
		ExplainRequirements: &pcs.AdmissionBenchmarkExplainReq{
			FailureCode: true, Expected: true, Actual: true,
			ResponsibleComponent: true, RepairHint: true,
		},
	}
	vr := pcs.VerificationResult{
		Status: pcs.StatusRejected,
		Checks: []pcs.VerificationCheck{{
			CheckID:     "trace_hash_alignment",
			Description: "TraceCertificate.trace_hash matches RuntimeReceipt.trace_hash",
			Status:      "failed",
			Details: map[string]any{
				"reason_code":                  pcs.ReasonTraceHashMismatch,
				"runtime_receipt_trace_hash": "sha256:aaa",
				"trace_certificate_trace_hash": "sha256:bbb",
			},
		}},
	}
	report := pcs.ExportPCSExplainQualityReport(pcs.ExportPCSExplainQualityCaseInput{
		Case: c, Result: pcs.AdmissionBenchmarkCaseResult{CaseID: c.CaseID, Kind: "invalid"},
		VR: &vr, SuiteID: "labtrust-qc-release", WorkflowID: "labtrust_qc_release",
		SourceCommit: pcs.ResolveSourceCommit(),
	})
	if report == nil || report.QualityScore < 0.8 {
		t.Fatalf("quality_score=%v gaps=%v", report.QualityScore, report.Gaps)
	}
	if err := pcs.ValidatePCSExplainQualityReport(root, *report); err != nil {
		t.Fatal(err)
	}
}

func TestExportPCSExplainQualityReportMissingHandoff(t *testing.T) {
	root := repoRoot(t)
	raw, err := os.ReadFile(filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release", "invalid", "missing_handoff.json"))
	if err != nil {
		t.Skip("missing_handoff case not materialized")
	}
	var caseData pcs.AdmissionBenchmarkCase
	if err := json.Unmarshal(raw, &caseData); err != nil {
		t.Fatal(err)
	}
	caseData.Kind = "invalid"
	report := pcs.ExportPCSExplainQualityReport(pcs.ExportPCSExplainQualityCaseInput{
		Case: caseData,
		Result: pcs.AdmissionBenchmarkCaseResult{
			CaseID: caseData.CaseID,
			Kind:   "invalid",
			Error:  `release_mode_handoff_required: profile "labtrust_qc_release" requires handoff kinds [bundle_to_verifier]`,
		},
		SuiteID:      "labtrust-qc-release",
		WorkflowID:   "labtrust_qc_release",
		SourceCommit: pcs.ResolveSourceCommit(),
	})
	if report == nil {
		t.Fatal("expected explain report")
	}
	if report.QualityScore < 0.8 {
		t.Fatalf("quality_score=%f want >=0.8 gaps=%v", report.QualityScore, report.Gaps)
	}
	if err := pcs.ValidatePCSExplainQualityReport(root, *report); err != nil {
		t.Fatal(err)
	}
}

func TestExportPCSExplainQualityReportMatchesSchema(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "formal_trust_kernel", "invalid")
	entries, err := os.ReadDir(casesDir)
	if err != nil {
		t.Skip("formal benchmark cases not materialized")
	}
	var caseData pcs.AdmissionBenchmarkCase
	for _, e := range entries {
		if e.Name() == "failed_lean_check.json" {
			raw, err := os.ReadFile(filepath.Join(casesDir, e.Name()))
			if err != nil {
				t.Fatal(err)
			}
			if err := json.Unmarshal(raw, &caseData); err != nil {
				t.Fatal(err)
			}
			break
		}
	}
	if caseData.CaseID == "" {
		t.Skip("failed_lean_check case missing")
	}
	caseData.Kind = "invalid"
	report := pcs.ExportPCSExplainQualityReport(pcs.ExportPCSExplainQualityCaseInput{
		Case:         caseData,
		Result:       pcs.AdmissionBenchmarkCaseResult{CaseID: caseData.CaseID, Kind: "invalid", Error: "lean_check_failed: lean check status Rejected (expected ProofChecked)"},
		SuiteID:      "formal-trust-kernel-v0",
		WorkflowID:   "formal_trust_kernel.enforcement_v0",
		SourceCommit: pcs.ResolveSourceCommit(),
	})
	if report == nil {
		t.Fatal("expected explain report")
	}
	if err := pcs.ValidatePCSExplainQualityReport(root, *report); err != nil {
		t.Fatal(err)
	}
	for _, section := range pcs.CanonicalExplainQualitySections {
		if !containsSection(report.RequiredSections, section) {
			t.Fatalf("expected section %s, got %v", section, report.RequiredSections)
		}
	}
}

func containsSection(sections []string, want string) bool {
	for _, s := range sections {
		if s == want {
			return true
		}
	}
	return false
}
