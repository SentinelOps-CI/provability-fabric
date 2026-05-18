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

func TestReleaseModeRequiresHandoff(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	manifest := loadReleaseManifest(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Registry:        loadArtifactRegistry(t),
	}
	_, err = pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err == nil || !strings.Contains(err.Error(), "--handoff") {
		t.Fatalf("expected handoff required error, got %v", err)
	}
}

func TestReleaseModeRequiresRegistry(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	loaded, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	manifest := loadReleaseManifest(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Handoff:         loaded,
	}
	_, err = pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err == nil || !strings.Contains(err.Error(), "--registry") {
		t.Fatalf("expected registry required error, got %v", err)
	}
}

func TestHandoffBundleHashMismatchRejected(t *testing.T) {
	loaded, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	loaded.Manifest.Invariants["certified_bundle_hash"] = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err = verifyWithLoadedHandoff(t, loaded)
	if err == nil || !strings.Contains(err.Error(), "certified_bundle_hash mismatch") {
		t.Fatalf("unexpected: %v", err)
	}
}

func TestRegistryWrongProducerRejected(t *testing.T) {
	TestPFRejectsWrongProducerForTraceCertificate(t)
}

func TestRegistryDisallowedStatusRejected(t *testing.T) {
	TestPFRejectsStatusNotAllowedByRegistry(t)
}

func TestReleaseChainResultValidatesAgainstPCSCore(t *testing.T) {
	TestReleaseChainValidationResultValidatesAgainstPCSCore(t)
}

func TestReleaseChainResultContainsRegistryChecks(t *testing.T) {
	artifactDir := filepath.Join(repoRoot(t), "..", "pcs-core", "examples", "labtrust-release")
	manifestPath := filepath.Join(artifactDir, "release_manifest.v0.json")
	if _, err := os.Stat(manifestPath); err != nil {
		manifestPath = validReleaseManifestPath(t)
		artifactDir = filepath.Dir(manifestPath)
	}
	opts := pcs.ReleaseChainVerifyOptions{
		RepoRoot:         repoRoot(t),
		ArtifactDir:      artifactDir,
		ValidatorVersion: pcs.DefaultVerifierVersion,
		SourceCommit:       loadReleaseManifest(t).PFSourceCommit,
		Registry:           loadArtifactRegistry(t),
		ReleaseMode:        true,
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	found := false
	for _, id := range pcs.RequiredReleaseChainCheckIDs {
		if id == "registry_admission_passed" {
			found = true
		}
		for _, c := range result.Checks {
			if c.CheckID == id {
				goto next
			}
		}
		t.Fatalf("missing required release chain check %q", id)
	next:
	}
	if !found {
		t.Fatal("registry_admission_passed must be a required check id")
	}
}

func TestPFExplainFailureOutputsRepairHint(t *testing.T) {
	path := labtrustReleaseFixture(t, "invalid_mismatched_trace_hash.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := releaseModeValidateOpts(t)
	opts.Handoff = nil
	opts.AllowMissingHandoff = true
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	explanations := pcs.ExplainVerificationFailures(result)
	if len(explanations) == 0 {
		t.Fatal("expected repair hints for failed verification")
	}
	if explanations[0].RepairHint == "" {
		t.Fatal("repair hint must not be empty")
	}
}

func mustLoadHandoff(t *testing.T) *pcs.LoadedHandoff {
	t.Helper()
	loaded, err := pcs.LoadHandoff(validHandoffManifestPath(t))
	if err != nil {
		t.Fatal(err)
	}
	return loaded
}
