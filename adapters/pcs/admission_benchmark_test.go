// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestAdmissionBenchmarkRequiredInvalidCasesMaterialized(t *testing.T) {
	root := repoRoot(t)
	present := map[string]bool{}
	workflows := []string{
		"labtrust_qc_release",
		"tool_use_safety",
		"computation_reproducibility",
		"formal_trust_kernel",
	}
	for _, wf := range workflows {
		invalidDir := filepath.Join(root, "benchmarks", "admission", wf, "invalid")
		entries, err := os.ReadDir(invalidDir)
		if err != nil {
			t.Fatalf("read %s: %v", invalidDir, err)
		}
		for _, e := range entries {
			if e.IsDir() || filepath.Ext(e.Name()) != ".json" {
				continue
			}
			present[e.Name()[:len(e.Name())-5]] = true
		}
	}
	for _, id := range pcs.RequiredAdmissionInvalidCaseIDs {
		if !present[id] {
			t.Fatalf("missing required invalid admission case %q (run scripts/materialize-admission-benchmark-cases.py)", id)
		}
	}
}

func TestAdmissionBenchmarkLabtrustSuite(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	run, _, cov, explain, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if run.Metrics.ValidReleaseAdmissionRate < 1.0 {
		t.Fatalf("valid admission rate=%v cases=%+v", run.Metrics.ValidReleaseAdmissionRate, failedCases(run))
	}
	if run.Metrics.InvalidReleaseRejectionRate < 0.85 {
		t.Fatalf("invalid rejection rate=%v cases=%+v", run.Metrics.InvalidReleaseRejectionRate, failedCases(run))
	}
	if err := pcs.ValidateAdmissionBenchmarkBundleDir(root, out); err != nil {
		t.Fatalf("bundle validation: %v", err)
	}
	if _, err := os.Stat(filepath.Join(out, "benchmark_report.v0.json")); err != nil {
		t.Fatal(err)
	}
	if cov.Registry.SemanticChecksExecuted == 0 && lastValidRCVR(run) {
		t.Fatal("expected registry semantic checks in coverage report")
	}
	if explain.MeanCompleteness <= 0 {
		t.Logf("explain mean completeness=%v (release-chain explain cases may be absent)", explain.MeanCompleteness)
	}
}

func TestAdmissionBenchmarkFormalTrustKernelSuite(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "formal_trust_kernel")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("formal trust kernel benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	run, _, _, explain, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if run.Metrics.ValidReleaseAdmissionRate < 1.0 {
		t.Fatalf("valid admission rate=%v cases=%+v", run.Metrics.ValidReleaseAdmissionRate, failedCases(run))
	}
	if run.Metrics.InvalidReleaseRejectionRate < 0.85 {
		t.Fatalf("invalid rejection rate=%v cases=%+v", run.Metrics.InvalidReleaseRejectionRate, failedCases(run))
	}
	if err := pcs.ValidateAdmissionBenchmarkBundleDir(root, out); err != nil {
		t.Fatalf("bundle validation: %v", err)
	}
	if explain.MeanCompleteness < 0.5 {
		t.Fatalf("expected measurable explain quality for formal cases, got %v", explain.MeanCompleteness)
	}
	for _, c := range run.Cases {
		if c.Kind == "invalid" && c.ExplainCompleteness == 0 {
			t.Logf("warning: no explain completeness scored for %s", c.CaseID)
		}
	}
}

func failedCases(run pcs.BenchmarkRunV0) []pcs.AdmissionBenchmarkCaseResult {
	var out []pcs.AdmissionBenchmarkCaseResult
	for _, c := range run.Cases {
		if !c.Passed {
			out = append(out, c)
		}
	}
	return out
}

func TestAdmissionBenchmarkToolUseSuite(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "tool_use_safety")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	run, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if run.Metrics.InvalidReleaseRejectionRate < 0.8 {
		t.Fatalf("invalid rejection rate=%v cases=%+v", run.Metrics.InvalidReleaseRejectionRate, failedCases(run))
	}
	if err := pcs.ValidateAdmissionBenchmarkBundleDir(root, out); err != nil {
		t.Fatal(err)
	}
}

func TestAdmissionBenchmarkComputationSuite(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "computation_reproducibility")
	if _, err := os.Stat(casesDir); err != nil {
		t.Skip("benchmark cases not materialized")
	}
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	run, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:     root,
		CasesDir:     casesDir,
		RegistryPath: reg,
		OutDir:       out,
	})
	if err != nil {
		t.Fatal(err)
	}
	if run.Metrics.InvalidReleaseRejectionRate < 0.8 {
		t.Fatalf("invalid rejection rate=%v cases=%+v", run.Metrics.InvalidReleaseRejectionRate, failedCases(run))
	}
	if err := pcs.ValidateAdmissionBenchmarkBundleDir(root, out); err != nil {
		t.Fatal(err)
	}
}

func lastValidRCVR(run pcs.BenchmarkRunV0) bool {
	for _, c := range run.Cases {
		if c.Kind == "valid" && c.ReleaseChainStatus == pcs.StatusProofChecked {
			return true
		}
	}
	return false
}
