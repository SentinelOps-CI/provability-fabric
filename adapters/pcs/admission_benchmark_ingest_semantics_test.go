// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
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
