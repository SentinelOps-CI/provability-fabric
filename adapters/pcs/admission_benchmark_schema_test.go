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
		"benchmark_report.v0.json",
		"benchmark_run.v0.json",
		"failure_localization_result.v0.json",
		"coverage_report.v0.json",
		"explain_quality_report.v0.json",
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
}
