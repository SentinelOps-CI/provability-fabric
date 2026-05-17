// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"os"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestDeterministicSignIsStable(t *testing.T) {
	t.Setenv("PF_SOURCE_COMMIT", "cccccccccccccccccccccccccccccccccccccccc")
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
		SourceCommit:    "cccccccccccccccccccccccccccccccccccccccc",
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	signOpts := pcs.SignOptions{BundlePath: path}
	signed1, err := pcs.SignVerificationResultWithOptions(root, bundle, result, signOpts)
	if err != nil {
		t.Fatal(err)
	}
	signed2, err := pcs.SignVerificationResultWithOptions(root, bundle, result, signOpts)
	if err != nil {
		t.Fatal(err)
	}
	if signed1.VerificationResult.VerificationID != signed2.VerificationResult.VerificationID {
		t.Fatalf("verification_id not stable: %q vs %q",
			signed1.VerificationResult.VerificationID, signed2.VerificationResult.VerificationID)
	}
	if signed1.SignedBundleID != signed2.SignedBundleID {
		t.Fatalf("signed_bundle_id not stable: %q vs %q", signed1.SignedBundleID, signed2.SignedBundleID)
	}
	if signed1.SignatureOrDigest != signed2.SignatureOrDigest {
		t.Fatalf("wrapper digest not stable")
	}
}

func TestNonDeterministicSignUsesRandomIDs(t *testing.T) {
	os.Unsetenv("PF_DETERMINISTIC")
	os.Unsetenv("PCS_DETERMINISTIC")
	os.Unsetenv("PF_SOURCE_COMMIT")

	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v", err)
	}
	signOpts := pcs.SignOptions{BundlePath: path}
	s1, err := pcs.SignVerificationResultWithOptions(root, bundle, result, signOpts)
	if err != nil {
		t.Fatal(err)
	}
	s2, err := pcs.SignVerificationResultWithOptions(root, bundle, result, signOpts)
	if err != nil {
		t.Fatal(err)
	}
	if s1.SignedBundleID == s2.SignedBundleID {
		t.Fatal("expected random signed_bundle_id when not in deterministic mode")
	}
}
