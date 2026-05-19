// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func computationReleaseArtifactDir(t *testing.T) string {
	t.Helper()
	root := repoRoot(t)
	for _, rel := range []string{
		filepath.Join("tests", "pcs", "fixtures", "computation-release"),
	} {
		dir := filepath.Join(root, rel)
		if _, err := os.Stat(filepath.Join(dir, "release_manifest.v0.json")); err == nil {
			return dir
		}
	}
	if pcsCore := pcsCoreRoot(t); pcsCore != "" {
		dir := filepath.Join(pcsCore, "examples", "computation-release")
		if _, err := os.Stat(filepath.Join(dir, "release_manifest.v0.json")); err == nil {
			return dir
		}
	}
	t.Skip("computation-release fixture dir not found (run scripts/pcs-sync-computation-release.py)")
	return ""
}

func loadComputationReleaseManifest(t *testing.T) *pcs.ReleaseManifest {
	t.Helper()
	dir := computationReleaseArtifactDir(t)
	path := filepath.Join(dir, "release_manifest.v0.json")
	m, err := pcs.LoadReleaseManifest(path)
	if err != nil {
		t.Fatal(err)
	}
	return m
}

func loadComputationArtifactRegistry(t *testing.T) *pcs.ArtifactRegistry {
	t.Helper()
	dir := computationReleaseArtifactDir(t)
	path := filepath.Join(dir, "artifact_registry.json")
	if _, err := os.Stat(path); err != nil {
		path = filepath.Join(pcsCoreRoot(t), "examples", "artifact_registry.valid.json")
	}
	reg, err := pcs.LoadArtifactRegistry(path)
	if err != nil {
		t.Fatal(err)
	}
	return reg
}

func runComputationReleaseChain(t *testing.T, releaseMode bool) pcs.ReleaseChainValidationResult {
	t.Helper()
	artifactDir := computationReleaseArtifactDir(t)
	manifestPath := filepath.Join(artifactDir, "release_manifest.v0.json")
	profile, err := pcs.LoadAdmissionProfile("scientific_computation_reproducibility")
	if err != nil {
		t.Fatal(err)
	}
	manifest := loadComputationReleaseManifest(t)
	pfCommit := manifest.ProducerRepos["provability_fabric"].Commit
	if pfCommit == "" {
		pfCommit = "c333333333333333333333333333333333333333"
	}
	opts := pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot(t),
		ArtifactDir:      artifactDir,
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:     pfCommit,
		Registry:         loadComputationArtifactRegistry(t),
		ReleaseMode:      releaseMode,
		AdmissionProfile: profile,
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	return result
}

func TestComputationProfileAdmitsPCSCoreReleaseBundle(t *testing.T) {
	dir := computationReleaseArtifactDir(t)
	bundlePath := filepath.Join(dir, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(bundlePath)
	if err != nil {
		t.Fatal(err)
	}
	profile, err := pcs.LoadAdmissionProfile("scientific_computation_reproducibility")
	if err != nil {
		t.Fatal(err)
	}
	handoff, err := pcs.LoadHandoff(filepath.Join(dir, "handoff_to_pf.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.HydrateComputationBundleFromDir(bundle, dir); err != nil {
		t.Fatal(err)
	}
	if err := pcs.EnforceAdmissionProfile(profile, bundlePath, bundle, handoff); err != nil {
		t.Fatalf("expected pcs-core computation release bundle to pass admission: %v", err)
	}
}

func TestComputationReleaseChainIncludesComputationChecks(t *testing.T) {
	result := runComputationReleaseChain(t, true)
	if result.Status != pcs.StatusProofChecked {
		for _, c := range result.Checks {
			if c.Status == "failed" {
				t.Logf("failed check %q: %v", c.CheckID, c.Details)
			}
		}
		t.Fatalf("status=%q failure_codes=%v", result.Status, result.FailureCodes)
	}
	want := []string{
		"computation_dataset_hash_consistent",
		"computation_environment_hash_consistent",
		"computation_result_hash_consistent",
		"computation_code_commit_present",
		"computation_exit_code_zero",
		"computation_witness_certificate_checked",
	}
	byID := map[string]pcs.ReleaseValidationCheck{}
	for _, c := range result.Checks {
		byID[c.CheckID] = c
	}
	for _, id := range want {
		c, ok := byID[id]
		if !ok {
			t.Fatalf("missing computation check %q", id)
		}
		if c.Status != "passed" {
			t.Fatalf("check %q status=%q details=%v", id, c.Status, c.Details)
		}
		if len(c.RegistryCheckRefs) == 0 {
			t.Fatalf("check %q missing registry_check_refs", id)
		}
	}
	if len(result.DeferredRegistryChecks) == 0 {
		t.Fatal("expected deferred_registry_checks in RCVR")
	}
}

func TestComputationReleaseChainRejectsHashMismatchFixture(t *testing.T) {
	root := repoRoot(t)
	path := filepath.Join(root, "tests", "pcs", "fixtures", "computation", "result_hash_mismatch.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	profile, err := pcs.LoadAdmissionProfile("scientific_computation_reproducibility")
	if err != nil {
		t.Fatal(err)
	}
	handoff, err := pcs.LoadHandoff(filepath.Join(computationReleaseArtifactDir(t), "handoff_to_pf.json"))
	if err != nil {
		t.Fatal(err)
	}
	err = pcs.EnforceAdmissionProfile(profile, path, bundle, handoff)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeResultHashMismatch) {
		t.Fatalf("expected result_hash_mismatch, got %v", err)
	}
}
