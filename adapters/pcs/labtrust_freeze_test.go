// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

// LabTrust canonical fixture freeze tests (PCS v0.1 release gate).
package pcs_test

import (
	"encoding/json"
	"errors"
	"os"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func TestVerifyLabtrustCanonicalBundlePasses(t *testing.T) {
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "cccccccccccccccccccccccccccccccccccccccc",
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected ProofChecked (pcs-core artifact_status), got %s", result.Status)
	}
}

func TestSignLabtrustBundleOutputsPCSCoreSignedBundle(t *testing.T) {
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify before sign: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	if signed.SchemaVersion != pcs.SchemaVersionV0 {
		t.Fatalf("signed schema_version want v0, got %s", signed.SchemaVersion)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed bundle must validate against pcs-core SignedScienceClaimBundle.v0: %v", err)
	}
	if len(signed.VerificationResult.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("PF sign must embed %d checks, got %d", len(pcs.RequiredCheckIDs), len(signed.VerificationResult.Checks))
	}
}

func TestInspectSignedLabtrustBundleSucceeds(t *testing.T) {
	path := labtrustFixture(t, "signed_science_claim_bundle.json")
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("pcs-core signed schema: %v", err)
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
		t.Fatalf("PF signed bundle integrity: %v", err)
	}
	summary := pcs.FormatInspectSummary(signed)
	if !strings.Contains(summary, "ProofChecked") {
		t.Fatalf("inspect summary missing ProofChecked: %s", summary)
	}
}

func TestLegacySingularRuntimeReceiptRejected(t *testing.T) {
	assertLegacyLoadRejected(t, "invalid_legacy_singular_runtime_receipt.json")
}

func TestLegacyTraceCertificateRejected(t *testing.T) {
	assertLegacyLoadRejected(t, "invalid_legacy_trace_certificate.json")
}

func TestLegacyTraceCertificatesRejected(t *testing.T) {
	assertLegacyLoadRejected(t, "invalid_legacy_trace_certificates.json")
}

func TestMismatchedTraceHashRejected(t *testing.T) {
	assertVerificationRejected(t, "invalid_mismatched_trace_hash.json", "trace_hash_alignment")
}

func TestFailedOrRejectedCertificateRejected(t *testing.T) {
	assertVerificationRejected(t, "invalid_rejected_certificate.json", "certificate_status_checked")
}

func TestMissingSignatureOrDigestRejected(t *testing.T) {
	assertVerificationRejected(t, "invalid_missing_signature_or_digest.json", "signature_or_digest_present")
}

func TestLabtrustSignedFixtureMatchesCertifiedBundle(t *testing.T) {
	cert, err := pcs.LoadScienceClaimBundle(labtrustFixture(t, "science_claim_bundle.certified.json"))
	if err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed.ScienceClaimBundle == nil {
		t.Fatal("missing embedded science_claim_bundle")
	}
	if signed.ScienceClaimBundle.BundleID != cert.BundleID {
		t.Fatalf("bundle_id mismatch: signed %q certified %q", signed.ScienceClaimBundle.BundleID, cert.BundleID)
	}
}

func TestRegenerateLabtrustSignedFixtureOptional(t *testing.T) {
	if os.Getenv("UPDATE_PCS_LABTRUST_SIGNED") != "1" {
		t.Skip("set UPDATE_PCS_LABTRUST_SIGNED=1 to rewrite tests/pcs/fixtures/labtrust/signed_science_claim_bundle.json")
	}
	path := labtrustFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	opts := pcs.ValidateOptions{RepoRoot: root, VerifierVersion: pcs.DefaultVerifierVersion, SourceCommit: "cccccccccccccccccccccccccccccccccccccccc"}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	data, err := json.MarshalIndent(signed, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	out := labtrustFixture(t, "signed_science_claim_bundle.json")
	if err := os.WriteFile(out, data, 0644); err != nil {
		t.Fatal(err)
	}
}

func assertLegacyLoadRejected(t *testing.T, name string) {
	t.Helper()
	_, err := pcs.LoadScienceClaimBundle(fixturePath(t, name))
	if err == nil {
		t.Fatalf("expected legacy load rejection for %s", name)
	}
	var legacy *pcs.LegacyBundleError
	if !errors.As(err, &legacy) {
		t.Fatalf("expected LegacyBundleError for %s, got %v", name, err)
	}
}

func assertVerificationRejected(t *testing.T, name, checkID string) {
	t.Helper()
	result := verifyFixture(t, name, false)
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected for %s, got %s", name, result.Status)
	}
	assertFailedCheck(t, result, checkID)
}
