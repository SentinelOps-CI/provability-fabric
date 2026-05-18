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

func TestReleaseModeRequiresHandoffManifest(t *testing.T) {
	TestReleaseModeRequiresHandoff(t)
}

func TestReleaseModeRequiresArtifactRegistry(t *testing.T) {
	TestReleaseModeRequiresRegistry(t)
}

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

func TestReleaseModeRejectsLegacyPFHandoff(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	legacyPath := labtrustReleaseFixture(t, "pf_handoff.json")
	loaded, err := pcs.LoadHandoff(legacyPath)
	if err != nil {
		t.Fatal(err)
	}
	if !loaded.IsLegacy() {
		t.Fatal("expected legacy pf_handoff fixture")
	}
	manifest := loadReleaseManifest(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Handoff:         loaded,
		Registry:        loadArtifactRegistry(t),
	}
	_, err = pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err == nil || !strings.Contains(err.Error(), pcs.FailureCodeLegacyHandoffForbiddenInReleaseMode) {
		t.Fatalf("expected legacy handoff forbidden, got %v", err)
	}
}

func TestLocalDevStillAcceptsLegacyHandoffWithWarning(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	legacyPath := labtrustReleaseFixture(t, "pf_handoff.json")
	loaded, err := pcs.LoadHandoff(legacyPath)
	if err != nil {
		t.Fatal(err)
	}
	manifest := loadReleaseManifest(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     false,
		Handoff:         loaded,
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected legacy handoff verify to pass outside release mode: %s", result.Status)
	}
	if pcs.LegacyHandoffWarning == "" {
		t.Fatal("expected legacy handoff warning constant")
	}
}

func TestRegistryWrongProducerRejected(t *testing.T) {
	TestPFRejectsWrongProducerForTraceCertificate(t)
}

func TestRegistryDisallowedStatusRejected(t *testing.T) {
	TestPFRejectsStatusNotAllowedByRegistry(t)
}

func TestRegistryMissingRequiredFieldRejected(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	bundle.SourceCommit = ""
	registry := loadArtifactRegistry(t)
	err = pcs.ValidateBundleAgainstRegistry(bundle, registry, pcs.RegistryValidateOptions{ReleaseMode: true})
	if err == nil || !strings.Contains(err.Error(), "required release field") {
		t.Fatalf("expected missing required field rejection, got %v", err)
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
		SourceCommit:     loadReleaseManifest(t).PFSourceCommit,
		Registry:         loadArtifactRegistry(t),
		ReleaseMode:      true,
	}
	result, err := pcs.VerifyReleaseChainFromManifest(manifestPath, opts)
	if err != nil {
		t.Fatal(err)
	}
	required := append([]string{}, pcs.RequiredReleaseChainCheckIDs...)
	for _, id := range required {
		found := false
		for _, c := range result.Checks {
			if c.CheckID == id {
				found = true
				break
			}
		}
		if !found {
			t.Fatalf("missing required release chain check %q", id)
		}
	}
	for _, id := range pcs.RegistryReleaseChainCheckIDs {
		found := false
		for _, c := range result.Checks {
			if c.CheckID == id {
				found = true
				break
			}
		}
		if !found {
			t.Fatalf("missing registry release chain check %q", id)
		}
	}
}

func TestPFExplainFailureContainsRepairCommand(t *testing.T) {
	TestPFExplainFailureOutputsRepairHint(t)
}

func TestPFExplainReleaseChainContainsRepairCommand(t *testing.T) {
	result := pcs.ReleaseChainValidationResult{
		Status: "Rejected",
		Checks: []pcs.ReleaseValidationCheck{{
			CheckID:     "manifest_hashes_match",
			Description: "All manifest artifact hashes match on-disk files",
			Status:      "failed",
			Details:     map[string]any{"failure_code": "PCS_MANIFEST_HASH_MISMATCH"},
		}},
	}
	explanations := pcs.ExplainReleaseChainFailures(result)
	if len(explanations) == 0 || explanations[0].RepairHint == "" {
		t.Fatal("expected release-chain repair hint")
	}
	if !strings.Contains(pcs.FormatFailureExplanations(explanations), "regenerate:") {
		t.Fatal("expected regenerate command in release-chain explain output")
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
	if explanations[0].RegenerateCmd == "" && !strings.Contains(pcs.FormatFailureExplanations(explanations), "regenerate:") {
		t.Fatal("expected regenerate command in explain output")
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
