// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestAdmissionBenchmarkOutputsMatchSchema(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	run, loc, cov, explain, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateBenchmarkRun(root, run); err != nil {
		t.Fatalf("benchmark run schema: %v", err)
	}
	if err := pcs.ValidateFailureLocalizationResult(root, loc); err != nil {
		t.Fatalf("localization schema: %v", err)
	}
	if err := pcs.ValidateCoverageReport(root, cov); err != nil {
		t.Fatalf("coverage schema: %v", err)
	}
	if err := pcs.ValidateExplainQualityReport(root, explain); err != nil {
		t.Fatalf("explain schema: %v", err)
	}
	for _, name := range []string{
		"benchmark_run.v0.json",
		"failure_localization_result.v0.json",
		"coverage_report.v0.json",
		"explain_quality_report.v0.json",
	} {
		if _, err := os.Stat(filepath.Join(out, name)); err != nil {
			t.Fatalf("missing output %s: %v", name, err)
		}
	}
}
