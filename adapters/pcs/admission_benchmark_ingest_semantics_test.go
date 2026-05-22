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

func TestPCSBenchIngestSemanticsLabtrustBundle(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	reg := validArtifactRegistryPath(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              casesDir,
		RegistryPath:          reg,
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
	if err := pcs.ValidatePCSBenchIngestSemantics(ingest); err != nil {
		t.Fatal(err)
	}
	for _, ref := range ingest.ArtifactRefs {
		if ref.SHA256 == "" || ref.Path == "" {
			t.Fatalf("incomplete artifact ref: %+v", ref)
		}
	}
	if ingest.SuiteID != "pf-labtrust-admission-v0" {
		t.Fatalf("suite_id=%q want pf-labtrust-admission-v0", ingest.SuiteID)
	}
	if ingest.WorkflowID != "hospital_lab.qc_release" {
		t.Fatalf("workflow_id=%q want hospital_lab.qc_release", ingest.WorkflowID)
	}
	for _, ref := range ingest.ArtifactRefs {
		if strings.Contains(ref.Path, `\`) {
			t.Fatalf("artifact ref path must use forward slashes: %q", ref.Path)
		}
	}
}

func TestPCSBenchIngestSemanticsRejectsMissingExplainRef(t *testing.T) {
	ingest := pcs.PCSBenchIngestV0{
		SchemaVersion:     pcs.SchemaVersionV0,
		ProducerID:        "provability-fabric",
		SuiteID:           "pf-admission-v0",
		WorkflowID:        "labtrust_qc_release",
		BenchmarkRuns:     []pcs.PCSBenchmarkRun{},
		CoverageReports:   []pcs.PCSCoverageReport{},
		ExplainQualityReports: []pcs.PCSExplainQualityReport{{
			SchemaVersion:         pcs.SchemaVersionV0,
			ReportID:              "explain-quality-test",
			SuiteID:               "pf-admission-v0",
			CaseID:                "test",
			ProducerID:            "provability-fabric",
			RequiredSections:      []string{"verification"},
			Sections:              map[string]pcs.PCSExplainSectionScore{"verification": {Present: true, Score: 1}},
			SectionsPresentCount:  1,
			SectionsRequiredCount: 1,
			QualityScore:          1,
			SourceRepo:            pcs.VerifierSourceRepo,
			SourceCommit:          pcs.ResolveSourceCommit(),
			SignatureOrDigest:     "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
		}},
		FailureLocalizationReports: []pcs.PCSFailureLocalizationResult{},
		ProfileCoverageReports:     []pcs.PCSProfileCoverageReport{},
		Commands:                   []pcs.PCSBenchmarkCommandEntry{},
		Logs:                       []string{},
		SourceRepo:                 pcs.VerifierSourceRepo,
		SourceCommit:               pcs.ResolveSourceCommit(),
		SignatureOrDigest:            "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
	}
	if err := pcs.ValidatePCSBenchIngestSemantics(ingest); err == nil {
		t.Fatal("expected missing artifact_refs for explain export")
	}
}

func TestPCSBenchIngestReleaseGradeWithPCSCorePython(t *testing.T) {
	root := repoRoot(t)
	pcsCore := pcsCoreRoot(t)
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release"),
		RegistryPath:          validArtifactRegistryPath(t),
		OutDir:                out,
		ValidatePCSCoreOutput: pcsCore,
	})
	if err != nil {
		t.Fatal(err)
	}
	script := filepath.Join(root, "scripts", "validate-pf-pcs-bench-ingest.py")
	if _, err := os.Stat(script); err != nil {
		t.Skip("validate-pf-pcs-bench-ingest.py not found")
	}
	ingest := filepath.Join(out, "pcs_bench_ingest.v0.json")
	pyExe, pyPrefix, ok := workingPythonForTests()
	if !ok {
		t.Skip("working python not on PATH")
	}
	args := append(pyPrefix, script,
		"--ingest", ingest,
		"--bundle-dir", out,
		"--pcs-core", pcsCore,
		"--release-grade",
	)
	cmd := exec.Command(pyExe, args...)
	cmd.Dir = root
	outBytes, runErr := cmd.CombinedOutput()
	if runErr != nil {
		t.Fatalf("release-grade ingest validation failed: %v\n%s", runErr, outBytes)
	}
}

func TestPCSBenchIngestValidatesWithPCSCorePython(t *testing.T) {
	pcsCore := pcsCoreRoot(t)
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              casesDir,
		RegistryPath:          validArtifactRegistryPath(t),
		OutDir:                out,
		ValidatePCSCoreOutput: pcsCore,
	})
	if err != nil {
		t.Fatal(err)
	}
	ingestPath := filepath.Join(out, "pcs_bench_ingest.v0.json")
	if _, err := os.Stat(ingestPath); err != nil {
		t.Fatal(err)
	}
	// When pcs-core python is on PATH, cross-check semantics the same way CI does.
	if os.Getenv("PCS_SKIP_PYTHON_INGEST_VALIDATE") != "" {
		t.Skip("PCS_SKIP_PYTHON_INGEST_VALIDATE set")
	}
}

func workingPythonForTests() (exe string, prefix []string, ok bool) {
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
