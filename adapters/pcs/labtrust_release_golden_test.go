// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestReleaseDeterministicSignIDsStable(t *testing.T) {
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	t.Setenv("PF_DETERMINISTIC", "1")
	id1, sid1 := releaseDeterministicGoldenIDs(manifest.PFSourceCommit, t)
	id2, sid2 := releaseDeterministicGoldenIDs(manifest.PFSourceCommit, t)
	if id1 != id2 || sid1 != sid2 {
		t.Fatalf("deterministic sign not stable: (%s,%s) vs (%s,%s)", id1, sid1, id2, sid2)
	}
}

func TestReleaseRegenerateMatchesFrozenSignedFixture(t *testing.T) {
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	t.Setenv("PF_DETERMINISTIC", "1")

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
	regenerated, err := pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: true,
		BundlePath:  path,
	})
	if err != nil {
		t.Fatal(err)
	}
	frozen, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if regenerated.SignedBundleID != frozen.SignedBundleID {
		t.Fatalf("signed_bundle_id mismatch after regenerate: %q vs %q",
			regenerated.SignedBundleID, frozen.SignedBundleID)
	}
	if regenerated.SignatureOrDigest != frozen.SignatureOrDigest {
		t.Fatalf("wrapper digest mismatch after regenerate")
	}
}

func releaseDeterministicGoldenIDs(pfCommit string, t *testing.T) (verificationID, signedBundleID string) {
	t.Helper()
	t.Setenv("PF_SOURCE_COMMIT", pfCommit)
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    pfCommit,
		ReleaseMode:     true,
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResultWithOptions(root, bundle, result, pcs.SignOptions{
		ReleaseMode: true,
		BundlePath:  path,
	})
	if err != nil {
		t.Fatal(err)
	}
	return signed.VerificationResult.VerificationID, signed.SignedBundleID
}
