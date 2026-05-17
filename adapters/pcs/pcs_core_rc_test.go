// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"crypto/sha256"
	"encoding/hex"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func fileSHA256Hex(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:]), nil
}

// Canonical pcs-core RC values (pcs-core/examples/labtrust-release).
const (
	rcCertifiedBundleHash = "sha256:9b42d792199eb6f358d26f822699f0ed65bb4366eee306d4958d42121c656833"
	rcCertificateID       = "cert-trace-886c95f0-5d63-42d6-aa13-5891c12c5a6a"
	rcTraceHash           = "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
	rcPFSourceCommit      = "0f659b90c80c46a6bbfd51b0d37ea723b032fb9d"
)

func pcsCoreRCDir(t *testing.T) string {
	t.Helper()
	dir := filepath.Join(repoRoot(t), "..", "pcs-core", "examples", "labtrust-release")
	if _, err := os.Stat(dir); err != nil {
		t.Skip("pcs-core/examples/labtrust-release not present")
	}
	return dir
}

func TestPFFixtureMatchesPCSCoreRC(t *testing.T) {
	rc := pcsCoreRCDir(t)
	for _, name := range []string{
		"science_claim_bundle.certified.json",
		"verification_result.json",
		"signed_science_claim_bundle.json",
	} {
		pfPath := labtrustReleaseFixture(t, name)
		rcPath := filepath.Join(rc, name)
		pfHash, err := fileSHA256Hex(pfPath)
		if err != nil {
			t.Fatal(err)
		}
		rcHash, err := fileSHA256Hex(rcPath)
		if err != nil {
			t.Fatal(err)
		}
		if pfHash != rcHash {
			t.Fatalf("%s digest mismatch: pf sha256:%s rc sha256:%s", name, pfHash, rcHash)
		}
	}
}

func TestPFVerifyAcceptsCanonicalRCBundle(t *testing.T) {
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
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil {
		t.Fatal(err)
	}
	if !pcs.VerificationPassed(result) {
		t.Fatalf("expected ProofChecked, got %s", result.Status)
	}
	if result.VerifiedInput == nil {
		t.Fatal("expected verified_input")
	}
	if result.VerifiedInput.BundleHash != rcCertifiedBundleHash {
		t.Fatalf("verified_input.bundle_hash %q != canonical %q", result.VerifiedInput.BundleHash, rcCertifiedBundleHash)
	}
	if result.VerifiedInput.CertificateID != rcCertificateID {
		t.Fatalf("verified_input.certificate_id %q != canonical %q", result.VerifiedInput.CertificateID, rcCertificateID)
	}
	if result.VerifiedInput.TraceHash != rcTraceHash {
		t.Fatalf("verified_input.trace_hash %q != canonical %q", result.VerifiedInput.TraceHash, rcTraceHash)
	}
	if result.SourceCommit != rcPFSourceCommit {
		t.Fatalf("source_commit %q != canonical %q", result.SourceCommit, rcPFSourceCommit)
	}
}

func TestPFInspectAcceptsCanonicalRCSignedBundle(t *testing.T) {
	path := labtrustReleaseFixture(t, "signed_science_claim_bundle.json")
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(repoRoot(t), signed); err != nil {
		t.Fatal(err)
	}
	if signed.SignedInputBundleHash != rcCertifiedBundleHash {
		t.Fatalf("signed_input_bundle_hash %q != canonical %q", signed.SignedInputBundleHash, rcCertifiedBundleHash)
	}
	if signed.SourceCommit != rcPFSourceCommit {
		t.Fatalf("source_commit %q != canonical %q", signed.SourceCommit, rcPFSourceCommit)
	}
	vi := signed.VerificationResult.VerifiedInput
	if vi == nil {
		t.Fatal("expected embedded verified_input")
	}
	if vi.CertificateID != rcCertificateID {
		t.Fatalf("verified_input.certificate_id %q != canonical %q", vi.CertificateID, rcCertificateID)
	}
	if vi.BundleHash != rcCertifiedBundleHash {
		t.Fatalf("verified_input.bundle_hash %q != canonical %q", vi.BundleHash, rcCertifiedBundleHash)
	}
	if vi.TraceHash != rcTraceHash {
		t.Fatalf("verified_input.trace_hash %q != canonical %q", vi.TraceHash, rcTraceHash)
	}

	rcPath := filepath.Join(pcsCoreRCDir(t), "signed_science_claim_bundle.json")
	pfHash, err := fileSHA256Hex(path)
	if err != nil {
		t.Fatal(err)
	}
	rcHash, err := fileSHA256Hex(rcPath)
	if err != nil {
		t.Fatal(err)
	}
	if pfHash != rcHash {
		t.Fatalf("signed bundle file digest mismatch: pf sha256:%s rc sha256:%s", pfHash, rcHash)
	}
}
