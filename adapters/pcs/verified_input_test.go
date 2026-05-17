// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestSignedBundleEmbedsExactCertifiedBundleCanonicalHash(t *testing.T) {
	certPath := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	certified, err := pcs.LoadScienceClaimBundle(certPath)
	if err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.AssertBundlesCanonicallyEqual(certified, signed.ScienceClaimBundle); err != nil {
		t.Fatal(err)
	}
}

func TestReleaseArtifactChainFromFixtures(t *testing.T) {
	certified, err := pcs.LoadScienceClaimBundle(labtrustReleaseFixture(t, "science_claim_bundle.certified.json"))
	if err != nil {
		t.Fatal(err)
	}
	vrBytes, err := os.ReadFile(labtrustReleaseFixture(t, "verification_result.json"))
	if err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	var result pcs.VerificationResult
	if err := json.Unmarshal(vrBytes, &result); err != nil {
		t.Fatal(err)
	}
	if err := pcs.AssertReleaseArtifactChain(certified, result, signed); err != nil {
		t.Fatal(err)
	}
}

func TestVerifyAndSignPreservesVerifiedInput(t *testing.T) {
	t.Setenv("PF_DETERMINISTIC", "1")
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)

	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	if result.VerifiedInput == nil {
		t.Fatal("expected verified_input on verification result")
	}
	signed, err := pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: true,
		BundlePath:  path,
	})
	if err != nil {
		t.Fatal(err)
	}
	if signed.SignedInputBundleHash != result.VerifiedInput.BundleHash {
		t.Fatalf("signed_input_bundle_hash mismatch")
	}
	if err := pcs.AssertReleaseArtifactChain(bundle, result, signed); err != nil {
		t.Fatal(err)
	}
}
