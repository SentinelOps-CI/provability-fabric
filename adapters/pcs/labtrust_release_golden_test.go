// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

// Golden IDs for scb-pcs-qc-release-v0.1 under PF_DETERMINISTIC=1 + fixture PF_SOURCE_COMMIT.
// Update only via make freeze-pcs-labtrust-release when intentional.
const (
	releaseGoldenVerificationID = "verification-31ac5758-9219-47cf-b832-0ca8ae07a871"
	releaseGoldenSignedBundleID   = "signed-bc8f7124-3571-4397-ae01-b7af1e9f5b6d"
)

func TestReleaseFrozenSignedIDsMatchDeterministicGolden(t *testing.T) {
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed.VerificationResult.VerificationID != releaseGoldenVerificationID {
		t.Fatalf("verification_id drift: got %q want %q (run make freeze-pcs-labtrust-release)",
			signed.VerificationResult.VerificationID, releaseGoldenVerificationID)
	}
	if signed.SignedBundleID != releaseGoldenSignedBundleID {
		t.Fatalf("signed_bundle_id drift: got %q want %q",
			signed.SignedBundleID, releaseGoldenSignedBundleID)
	}
}

func TestReleaseRegenerateMatchesFrozenSignedFixture(t *testing.T) {
	t.Setenv("PF_SOURCE_COMMIT", "cccccccccccccccccccccccccccccccccccccccc")
	t.Setenv("PF_DETERMINISTIC", "1")
	t.Setenv("PCS_DETERMINISTIC", "1")

	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "cccccccccccccccccccccccccccccccccccccccc",
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	regenerated, err := pcs.SignVerificationResult(root, bundle, result)
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
