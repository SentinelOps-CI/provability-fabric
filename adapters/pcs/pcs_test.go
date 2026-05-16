// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func repoRoot(t *testing.T) string {
	t.Helper()
	wd, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	root, err := pcs.FindRepoRoot(wd)
	if err != nil {
		// tests may run from adapters/pcs
		root, err = pcs.FindRepoRoot(filepath.Join(wd, "..", ".."))
	}
	if err != nil {
		t.Fatal(err)
	}
	return root
}

func fixturePath(t *testing.T, name string) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "tests", "pcs", name)
}

func verifyFixture(t *testing.T, name string) pcs.VerificationResult {
	t.Helper()
	path := fixturePath(t, name)
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatalf("load %s: %v", name, err)
	}
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "test",
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatalf("verify %s: %v", name, err)
	}
	return result
}

func TestValidLabTrustBundlePasses(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json")
	if result.Status != "passed" {
		t.Fatalf("expected passed, got %s", result.Status)
	}
}

func TestMissingAssumptionRejected(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_assumption.json")
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertAnyFailedCheck(t, result, "pcs.presence.assumption_set", "pcs.schema.science_claim_bundle")
}

func TestMissingCertificateRejected(t *testing.T) {
	result := verifyFixture(t, "invalid_missing_certificate.json")
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "pcs.presence.trace_certificate")
}

func TestMismatchedTraceHashRejected(t *testing.T) {
	result := verifyFixture(t, "invalid_mismatched_trace_hash.json")
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "pcs.certificate.trace_hash_match")
}

func TestRejectedCertificateRejected(t *testing.T) {
	result := verifyFixture(t, "invalid_rejected_certificate.json")
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "pcs.certificate.status_checked")
}

func TestStaleArtifactRejected(t *testing.T) {
	result := verifyFixture(t, "invalid_stale_artifact.json")
	if result.Status != "failed" {
		t.Fatalf("expected failed, got %s", result.Status)
	}
	assertFailedCheck(t, result, "pcs.artifact.not_stale")
}

func TestSignedResultRoundTrip(t *testing.T) {
	path := fixturePath(t, "valid_labtrust_bundle.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := pcs.ValidateOptions{RepoRoot: repoRoot(t), VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "test"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || result.Status != "passed" {
		t.Fatalf("verification failed: %v status=%s", err, result.Status)
	}
	root := repoRoot(t)
	signed, err := pcs.SignVerificationResult(root, path, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	if signed.SignatureOrDigest == "" {
		t.Fatal("expected wrapper digest")
	}
	if err := pcs.VerifySignedBundleIntegrity(signed); err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed schema: %v", err)
	}
}

func TestSignRefusesFailedVerification(t *testing.T) {
	path := fixturePath(t, "invalid_missing_certificate.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "test"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || result.Status != "failed" {
		t.Fatalf("expected failed verification")
	}
	if _, err := pcs.SignVerificationResult(root, path, bundle, result); err == nil {
		t.Fatal("expected sign to fail for failed verification")
	}
}

func TestVerificationResultSnapshot(t *testing.T) {
	result := verifyFixture(t, "valid_labtrust_bundle.json")
	// Stable fields for snapshot comparison
	result.VerificationID = "00000000-0000-0000-0000-000000000001"
	result.CreatedAt = "2026-05-16T12:00:00Z"
	result.SourceCommit = "test-commit"
	result.SignatureOrDigest = "sha256:snapshot-digest"

	data, err := json.MarshalIndent(result, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	snapshot := filepath.Join(repoRoot(t), "tests", "pcs", "testdata", "valid_verification_result.snapshot.json")
	if os.Getenv("UPDATE_PCS_SNAPSHOTS") == "1" {
		_ = os.MkdirAll(filepath.Dir(snapshot), 0755)
		if err := os.WriteFile(snapshot, data, 0644); err != nil {
			t.Fatal(err)
		}
		return
	}
	expected, err := os.ReadFile(snapshot)
	if err != nil {
		t.Fatalf("missing snapshot %s (run with UPDATE_PCS_SNAPSHOTS=1): %v", snapshot, err)
	}
	if strings.TrimSpace(string(expected)) != strings.TrimSpace(string(data)) {
		t.Fatalf("snapshot mismatch for valid bundle verification result")
	}
}

func assertFailedCheck(t *testing.T, result pcs.VerificationResult, id string) {
	t.Helper()
	assertAnyFailedCheck(t, result, id)
}

func assertAnyFailedCheck(t *testing.T, result pcs.VerificationResult, ids ...string) {
	t.Helper()
	for _, id := range ids {
		for _, c := range result.Checks {
			if c.CheckID == id && c.Status == pcs.CheckFailed {
				return
			}
		}
	}
	t.Fatalf("expected one of %v to fail in %+v", ids, result.Checks)
}
