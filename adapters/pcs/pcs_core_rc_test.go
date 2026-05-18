// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

// Canonical pcs-core RC values (pcs-core/examples/labtrust-release).
const (
	rcCertifiedBundleHash = "sha256:9b42d792199eb6f358d26f822699f0ed65bb4366eee306d4958d42121c656833"
	rcCertificateID       = "cert-trace-886c95f0-5d63-42d6-aa13-5891c12c5a6a"
	rcTraceHash           = "sha256:c3e8a3dc4ad86d533de1dfa4ae7fe2a338c2cff3c945404c96a75216524d58cd"
	rcPFSourceCommit      = "0f659b90c80c46a6bbfd51b0d37ea723b032fb9d"
)

func fileSHA256Hex(path string) (string, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return "", err
	}
	sum := sha256.Sum256(data)
	return hex.EncodeToString(sum[:]), nil
}

func pcsCoreRCDir(t *testing.T) string {
	t.Helper()
	dir := filepath.Join(pcsCoreRoot(t), "examples", "labtrust-release")
	if _, err := os.Stat(dir); err != nil {
		t.Skipf("pcs-core RC dir not present: %s", dir)
	}
	return dir
}

func assertFilesMatchRC(t *testing.T, pfPath, rcPath string) {
	t.Helper()
	pfBytes, err := os.ReadFile(pfPath)
	if err != nil {
		t.Fatal(err)
	}
	rcBytes, err := os.ReadFile(rcPath)
	if err != nil {
		t.Fatal(err)
	}
	if bytes.Equal(pfBytes, rcBytes) {
		return
	}
	pfHash, err := fileSHA256Hex(pfPath)
	if err != nil {
		t.Fatal(err)
	}
	rcHash, err := fileSHA256Hex(rcPath)
	if err != nil {
		t.Fatal(err)
	}
	if pfHash == rcHash {
		t.Logf("byte layout differs but sha256 matches (pf %d bytes, rc %d bytes)", len(pfBytes), len(rcBytes))
		return
	}
	t.Fatalf("file drift: pf sha256:%s rc sha256:%s (pf %d bytes, rc %d bytes)", pfHash, rcHash, len(pfBytes), len(rcBytes))
}

func TestPFLabtrustReleaseFixtureMatchesPCSCoreRC(t *testing.T) {
	rc := pcsCoreRCDir(t)
	pfPath := labtrustReleaseFixture(t, "signed_science_claim_bundle.json")
	rcPath := filepath.Join(rc, "signed_science_claim_bundle.json")
	assertFilesMatchRC(t, pfPath, rcPath)
}

func TestPFSignedBundleRCIdentity(t *testing.T) {
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
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
		t.Fatal("verification_result.verified_input is required")
	}
	assertCanonicalRCFields(t, vi.BundleHash, vi.CertificateID, vi.TraceHash, signed.VerificationResult.SourceCommit)
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
		t.Fatal(err)
	}

	vrPath := labtrustReleaseFixture(t, "verification_result.json")
	vrBytes, err := os.ReadFile(vrPath)
	if err != nil {
		t.Fatal(err)
	}
	var standalone pcs.VerificationResult
	if err := json.Unmarshal(vrBytes, &standalone); err != nil {
		t.Fatal(err)
	}
	if standalone.VerifiedInput == nil {
		t.Fatal("standalone verification_result.verified_input is required")
	}
	assertCanonicalRCFields(t, standalone.VerifiedInput.BundleHash, standalone.VerifiedInput.CertificateID, standalone.VerifiedInput.TraceHash, standalone.SourceCommit)
}

func assertCanonicalRCFields(t *testing.T, bundleHash, certID, traceHash, sourceCommit string) {
	t.Helper()
	if bundleHash != rcCertifiedBundleHash {
		t.Fatalf("verified_input.bundle_hash %q != canonical %q", bundleHash, rcCertifiedBundleHash)
	}
	if certID != rcCertificateID {
		t.Fatalf("verified_input.certificate_id %q != canonical %q", certID, rcCertificateID)
	}
	if traceHash != rcTraceHash {
		t.Fatalf("verified_input.trace_hash %q != canonical %q", traceHash, rcTraceHash)
	}
	if sourceCommit != rcPFSourceCommit {
		t.Fatalf("verification_result.source_commit %q != canonical %q", sourceCommit, rcPFSourceCommit)
	}
}
