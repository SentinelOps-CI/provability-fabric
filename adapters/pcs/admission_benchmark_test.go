// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

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
	if _, err := os.Stat(filepath.Join(out, "benchmark_run.v0.json")); err != nil {
		t.Fatal(err)
	}
	if cov.Registry.SemanticChecksExecuted == 0 && lastValidRCVR(run) {
		t.Fatal("expected registry semantic checks in coverage report")
	}
	if explain.MeanCompleteness <= 0 {
		t.Logf("explain mean completeness=%v (release-chain explain cases may be absent)", explain.MeanCompleteness)
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
}

func lastValidRCVR(run pcs.BenchmarkRunV0) bool {
	for _, c := range run.Cases {
		if c.Kind == "valid" && c.ReleaseChainStatus == pcs.StatusProofChecked {
			return true
		}
	}
	return false
}

