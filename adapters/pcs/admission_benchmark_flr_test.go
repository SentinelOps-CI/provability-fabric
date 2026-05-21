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

func TestFailureLocalizationBundleHashMismatchGoldStandard(t *testing.T) {
	root := repoRoot(t)
	casesDir := filepath.Join(root, "benchmarks", "admission", "labtrust_qc_release")
	out := t.TempDir()
	_, _, _, _, err := pcs.RunAdmissionBenchmark(pcs.AdmissionBenchmarkOptions{
		RepoRoot:              root,
		CasesDir:              casesDir,
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
	var flr *pcs.PCSFailureLocalizationResult
	for i := range ingest.FailureLocalizationReports {
		if ingest.FailureLocalizationReports[i].CaseID == "bundle_hash_mismatch" {
			flr = &ingest.FailureLocalizationReports[i]
			break
		}
	}
	if flr == nil {
		t.Fatal("missing bundle_hash_mismatch failure localization report")
	}
	if flr.ExpectedFailureCode != "signed_input_bundle_hash_match" {
		t.Fatalf("expected_failure_code=%q", flr.ExpectedFailureCode)
	}
	if flr.ObservedFailureCode != "signed_input_bundle_hash_match" {
		t.Fatalf("observed_failure_code=%q", flr.ObservedFailureCode)
	}
	if flr.ExpectedResponsibleComponent != "hashing" {
		t.Fatalf("expected_responsible_component=%q want hashing", flr.ExpectedResponsibleComponent)
	}
	if flr.ObservedResponsibleComponent != "hashing" {
		t.Fatalf("observed_responsible_component=%q want hashing", flr.ObservedResponsibleComponent)
	}
	if !flr.LocalizedCorrectly {
		t.Fatalf("localized_correctly=false for bundle_hash_mismatch")
	}
}

func TestFailureLocalizationAccuracyLabtrust(t *testing.T) {
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
	if run.Metrics.FailureLocalizationAccuracy < 0.85 {
		t.Fatalf("failure_localization_accuracy=%f want >=0.85", run.Metrics.FailureLocalizationAccuracy)
	}
}

func TestExportPCSBenchIngestReferenceArtifact(t *testing.T) {
	root := repoRoot(t)
	path := filepath.Join(root, "benchmarks", "admission", "examples", "labtrust_qc_release.pcs_bench_ingest.reference.json")
	if _, err := os.Stat(path); err != nil {
		t.Skip("reference ingest not materialized; run scripts/export-pcs-benchmark-ingest-reference.sh")
	}
	if err := pcs.ValidateBenchmarkArtifactFile(root, path); err != nil {
		t.Fatal(err)
	}
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var ingest pcs.PCSBenchIngestV0
	if err := json.Unmarshal(data, &ingest); err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidatePCSBenchIngestSemantics(ingest); err != nil {
		t.Fatal(err)
	}
}
