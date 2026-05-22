// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestLabtrustRequiredFailureFamiliesMaterialized(t *testing.T) {
	root := repoRoot(t)
	invalidDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release", "invalid")
	present := map[string]bool{}
	entries, err := os.ReadDir(invalidDir)
	if err != nil {
		t.Fatalf("read %s: %v", invalidDir, err)
	}
	for _, e := range entries {
		if e.IsDir() || filepath.Ext(e.Name()) != ".json" {
			continue
		}
		present[strings.TrimSuffix(e.Name(), ".json")] = true
	}
	for _, id := range pcs.LabtrustRequiredFailureFamilyCaseIDs {
		if !present[id] {
			t.Fatalf("labtrust suite missing failure-family case %q", id)
		}
	}
	validPath := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release", "valid", "release_chain.json")
	if _, err := os.Stat(validPath); err != nil {
		t.Fatalf("labtrust suite missing valid release case: %v", err)
	}
}

func TestLabtrustFailureFamiliesRejectedInBenchmark(t *testing.T) {
	root := repoRoot(t)
	out := t.TempDir()
	run, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release"),
		RegistryPath:          validArtifactRegistryPath(t),
		OutDir:                out,
		RequireAllCasesPass:   true,
		ValidatePCSCoreOutput: pcsCoreRoot(t),
	})
	if err != nil {
		t.Fatal(err)
	}
	if run.Metrics.ValidReleaseAdmissionRate < 1.0 {
		t.Fatalf("valid_release_admission_rate=%v", run.Metrics.ValidReleaseAdmissionRate)
	}
	if run.Metrics.InvalidReleaseRejectionRate < 1.0 {
		t.Fatalf("invalid_release_rejection_rate=%v", run.Metrics.InvalidReleaseRejectionRate)
	}
	byID := map[string]pcs.AdmissionBenchmarkCaseResult{}
	for _, c := range run.Cases {
		byID[c.CaseID] = c
	}
	for _, id := range pcs.LabtrustRequiredFailureFamilyCaseIDs {
		cr, ok := byID[id]
		if !ok {
			t.Fatalf("benchmark run missing case %q", id)
		}
		if cr.Kind != "invalid" || !cr.Passed {
			t.Fatalf("case %q: kind=%q passed=%v outcome=%s", id, cr.Kind, cr.Passed, cr.Outcome)
		}
	}
}

func TestLabtrustIngestCommandsUsePortablePaths(t *testing.T) {
	root := repoRoot(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release"),
		RegistryPath:          validArtifactRegistryPath(t),
		OutDir:                out,
		ValidatePCSCoreOutput: pcsCoreRoot(t),
	})
	if err != nil {
		t.Fatal(err)
	}
	ingest, err := pcs.LoadPCSBenchIngestFromDir(out)
	if err != nil {
		t.Fatal(err)
	}
	for i, cmd := range ingest.Commands {
		if strings.Contains(cmd.Command, `\`) {
			t.Fatalf("commands[%d] contains backslash path: %q", i, cmd.Command)
		}
		if !strings.Contains(cmd.Command, "benchmarks/admission/labtrust_qc_release") {
			t.Fatalf("commands[%d] expected repo-relative cases path: %q", i, cmd.Command)
		}
	}
	for _, run := range ingest.BenchmarkRuns {
		for _, cmd := range run.Commands {
			if strings.Contains(cmd.Command, `\`) {
				t.Fatalf("run %s command contains backslash: %q", run.CaseID, cmd.Command)
			}
		}
	}
}

func TestLabtrustReferenceIngestProducerContract(t *testing.T) {
	root := repoRoot(t)
	ref := filepath.Join(root, "benchmarks", "admission", "examples", "labtrust_qc_release.pcs_bench_ingest.reference.json")
	if _, err := os.Stat(ref); err != nil {
		t.Skip("reference ingest not materialized; run make export-pcs-benchmark-ingest-reference")
	}
	script := filepath.Join(root, "scripts", "pcs-bench-producer-contract-check.py")
	if _, err := os.Stat(script); err != nil {
		t.Fatal(err)
	}
	bundle := filepath.Join(root, "benchmark_runs", "labtrust_admission")
	pyExe, pyPrefix, ok := workingPythonForContractTest()
	if !ok {
		t.Skip("working python not on PATH")
	}
	args := append(pyPrefix, script, "--ingest", ref, "--bundle-dir", bundle)
	cmd := exec.Command(pyExe, args...)
	cmd.Dir = root
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("producer contract check failed: %v\n%s", err, out)
	}
}

func workingPythonForContractTest() (exe string, prefix []string, ok bool) {
	candidates := []struct {
		exe    string
		prefix []string
	}{
		{"python3", nil},
		{"python", nil},
		{"py", []string{"-3"}},
	}
	for _, c := range candidates {
		path, err := exec.LookPath(c.exe)
		if err != nil {
			continue
		}
		args := append(append([]string{}, c.prefix...), "-c", "import sys")
		if exec.Command(path, args...).Run() != nil {
			continue
		}
		return path, c.prefix, true
	}
	return "", nil, false
}

func TestLabtrustIngestArtifactRefRoles(t *testing.T) {
	root := repoRoot(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release"),
		RegistryPath:          validArtifactRegistryPath(t),
		OutDir:                out,
		ValidatePCSCoreOutput: pcsCoreRoot(t),
	})
	if err != nil {
		t.Fatal(err)
	}
	ingest, err := pcs.LoadPCSBenchIngestFromDir(out)
	if err != nil {
		t.Fatal(err)
	}
	rolesByType := map[string]map[string]int{}
	for _, ref := range ingest.ArtifactRefs {
		rolesByType[ref.ArtifactType] = map[string]int{}
	}
	for _, ref := range ingest.ArtifactRefs {
		rolesByType[ref.ArtifactType][ref.Role]++
	}
	if rolesByType["BenchmarkRun.v0"]["primary"] == 0 {
		t.Fatal("expected BenchmarkRun.v0 refs with role primary")
	}
	if rolesByType["ProfileCoverageReport.v0"]["ingest_bundle"] == 0 {
		t.Fatal("expected ProfileCoverageReport.v0 ref with role ingest_bundle")
	}
	if rolesByType["CoverageReport.v0"]["producer_export"] == 0 {
		t.Fatal("expected CoverageReport.v0 refs with role producer_export")
	}
}
