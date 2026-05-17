// SPDX-License-Identifier: Apache-2.0
// Copyright 2025 Provability-Fabric Contributors

package pcs_test

import (
	"encoding/json"
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"

	pcs "github.com/SentinelOps-CI/provability-fabric/adapters/pcs"
)

func labtrustReleaseFixture(t *testing.T, name string) string {
	t.Helper()
	return filepath.Join(repoRoot(t), "tests", "pcs", "fixtures", "labtrust-release", name)
}

// LabTrust + CertifyEdge release fixture freeze tests (PCS v0.1 release gate).

func TestVerifyLabtrustReleaseCertifiedBundlePasses(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
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
		t.Fatalf("expected ProofChecked, got %s", result.Status)
	}
}

func TestValidateReleaseVerificationResultSchema(t *testing.T) {
	path := labtrustReleaseFixture(t, "verification_result.json")
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	var result pcs.VerificationResult
	if err := json.Unmarshal(data, &result); err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateVerificationResult(repoRoot(t), result); err != nil {
		t.Fatalf("verification result schema: %v", err)
	}
	if result.Status != "ProofChecked" {
		t.Fatalf("expected ProofChecked, got %s", result.Status)
	}
	if len(result.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("expected %d PF checks in frozen result, got %d", len(pcs.RequiredCheckIDs), len(result.Checks))
	}
}

func TestValidateReleaseSignedBundleSchema(t *testing.T) {
	path := labtrustReleaseFixture(t, "signed_science_claim_bundle.json")
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed bundle schema: %v", err)
	}
	if err := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true}); err != nil {
		t.Fatalf("signed bundle integrity: %v", err)
	}
}

func TestReleaseSignedBundleProvenance(t *testing.T) {
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed.SourceRepo != pcs.VerifierSourceRepo {
		t.Fatalf("source_repo want %q, got %q", pcs.VerifierSourceRepo, signed.SourceRepo)
	}
	if strings.TrimSpace(signed.SourceCommit) == "" {
		t.Fatal("source_commit must be set on signed wrapper")
	}
	if strings.TrimSpace(signed.SignatureOrDigest) == "" || !strings.HasPrefix(signed.SignatureOrDigest, "sha256:") {
		t.Fatalf("signature_or_digest must be sha256 digest, got %q", signed.SignatureOrDigest)
	}
	if signed.VerificationResult.SourceRepo != pcs.VerifierSourceRepo {
		t.Fatalf("verification_result.source_repo want PF repo")
	}
}

func TestSignLabtrustReleaseBundleOutputsPCSCoreSignedBundle(t *testing.T) {
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	root := repoRoot(t)
	t.Setenv("PF_SOURCE_COMMIT", "cccccccccccccccccccccccccccccccccccccccc")
	t.Setenv("PF_DETERMINISTIC", "1")
	opts := pcs.ValidateOptions{
		RepoRoot:        root,
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    "cccccccccccccccccccccccccccccccccccccccc",
	}
	result, err := pcs.VerifyScienceClaimBundle(path, bundle, opts)
	if err != nil || !pcs.VerificationPassed(result) {
		t.Fatalf("verify before sign: %v status=%s", err, result.Status)
	}
	signed, err := pcs.SignVerificationResult(root, bundle, result)
	if err != nil {
		t.Fatal(err)
	}
	if err := pcs.ValidateSignedScienceClaimBundle(root, signed); err != nil {
		t.Fatalf("signed bundle schema: %v", err)
	}
	if len(signed.VerificationResult.Checks) != len(pcs.RequiredCheckIDs) {
		t.Fatalf("PF sign must embed %d checks, got %d", len(pcs.RequiredCheckIDs), len(signed.VerificationResult.Checks))
	}
}

func TestReleaseSignedFixtureMatchesCertifiedBundle(t *testing.T) {
	cert, err := pcs.LoadScienceClaimBundle(labtrustReleaseFixture(t, "science_claim_bundle.certified.json"))
	if err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed.ScienceClaimBundle == nil {
		t.Fatal("missing embedded science_claim_bundle")
	}
	if signed.ScienceClaimBundle.BundleID != cert.BundleID {
		t.Fatalf("bundle_id mismatch: signed %q certified %q", signed.ScienceClaimBundle.BundleID, cert.BundleID)
	}
	if signed.VerificationResult.BundleID != cert.BundleID {
		t.Fatalf("verification bundle_id mismatch")
	}
}

func TestRegenerateLabtrustReleaseFixturesOptional(t *testing.T) {
	if os.Getenv("UPDATE_PCS_LABTRUST_RELEASE") != "1" {
		t.Skip("set UPDATE_PCS_LABTRUST_RELEASE=1 to run make freeze-pcs-labtrust-release")
	}
	t.Skip("run: make freeze-pcs-labtrust-release (requires LabTrust-Gym release/)")
}

func TestInspectReleaseSignedBundleSucceeds(t *testing.T) {
	path := labtrustReleaseFixture(t, "signed_science_claim_bundle.json")
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	summary := pcs.FormatInspectSummary(signed)
	if !strings.Contains(summary, "ProofChecked") || !strings.Contains(summary, "scb-pcs-qc-release-v0.1") {
		t.Fatalf("inspect summary: %s", summary)
	}
}

func TestReleaseStaleArtifactRejected(t *testing.T) {
	assertVerificationRejectedRelease(t, "invalid_stale_artifact.json", "artifact_not_stale")
}

func TestReleaseLegacySingularRuntimeReceiptRejected(t *testing.T) {
	assertLegacyLoadRejectedRelease(t, "invalid_singular_runtime_receipt_bundle.json")
}

func TestReleaseLegacyTraceCertificateSingularRejected(t *testing.T) {
	assertLegacyLoadRejectedRelease(t, "invalid_trace_certificate_singular_bundle.json")
}

func TestReleaseMismatchedTraceHashRejected(t *testing.T) {
	assertVerificationRejectedRelease(t, "invalid_mismatched_trace_hash.json", "trace_hash_alignment")
}

func TestReleaseMissingSignatureOrDigestRejected(t *testing.T) {
	assertVerificationRejectedRelease(t, "invalid_missing_signature_or_digest.json", "signature_or_digest_present")
}

func TestReleaseZeroSourceCommitRejected(t *testing.T) {
	assertVerificationRejectedRelease(t, "invalid_zero_source_commit_release.json", "source_commit_not_placeholder")
}

func TestReleaseRejectedCertificateRejected(t *testing.T) {
	assertVerificationRejectedRelease(t, "invalid_rejected_certificate.json", "certificate_status_checked")
}

func assertLegacyLoadRejectedRelease(t *testing.T, name string) {
	t.Helper()
	_, err := pcs.LoadScienceClaimBundle(labtrustReleaseFixture(t, name))
	if err == nil {
		t.Fatal("expected legacy load rejection")
	}
	var legacy *pcs.LegacyBundleError
	if !errors.As(err, &legacy) {
		t.Fatalf("expected LegacyBundleError, got %v", err)
	}
}

func assertVerificationRejectedRelease(t *testing.T, name, checkID string) {
	t.Helper()
	path := labtrustReleaseFixture(t, name)
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatalf("load %s: %v", name, err)
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
	if pcs.VerificationPassed(result) {
		t.Fatalf("expected Rejected for %s, got %s", name, result.Status)
	}
	assertFailedCheck(t, result, checkID)
}

func TestCleanChainPFSegmentOnReleaseFixtures(t *testing.T) {
	root := repoRoot(t)
	release := filepath.Join(root, "tests", "pcs", "fixtures", "labtrust-release")
	pcsCore := filepath.Join(filepath.Dir(root), "pcs-core")
	env := append(os.Environ(),
		"PF_SOURCE_COMMIT=cccccccccccccccccccccccccccccccccccccccc",
		"PCS_CORE_PATH="+pcsCore,
	)
	var cmd *exec.Cmd
	if runtime.GOOS == "windows" {
		ps1 := filepath.Join(root, "scripts", "pcs-pf-clean-chain.ps1")
		if _, err := os.Stat(ps1); err != nil {
			t.Skip("pcs-pf-clean-chain.ps1 not found")
		}
		cmd = exec.Command("powershell", "-NoProfile", "-ExecutionPolicy", "Bypass", "-File", ps1, release)
		cmd.Dir = root
		cmd.Env = env
	} else {
		script := filepath.Join(root, "scripts", "pcs-pf-clean-chain.sh")
		if _, err := os.Stat(script); err != nil {
			t.Skip("pcs-pf-clean-chain.sh not found")
		}
		cmd = exec.Command("bash", script, release)
		cmd.Env = append(env, "PF=go -C "+filepath.Join(root, "core", "cli", "pf")+" run .")
	}
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("PF clean-chain segment failed: %v\n%s", err, out)
	}
	for _, name := range []string{"verification_result.json", "signed_science_claim_bundle.json"} {
		if _, err := os.Stat(filepath.Join(release, name)); err != nil {
			t.Fatalf("missing %s after PF clean-chain segment", name)
		}
	}
}
