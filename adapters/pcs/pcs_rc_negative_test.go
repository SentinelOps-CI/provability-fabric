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

func verifyWithHandoff(t *testing.T, handoff *pcs.PFHandoff) error {
	t.Helper()
	manifest := loadReleaseManifest(t)
	t.Setenv("PF_SOURCE_COMMIT", manifest.PFSourceCommit)
	path := labtrustReleaseFixture(t, "science_claim_bundle.certified.json")
	bundle, err := pcs.LoadScienceClaimBundle(path)
	if err != nil {
		t.Fatal(err)
	}
	opts := pcs.ValidateOptions{
		RepoRoot:        repoRoot(t),
		VerifierVersion: pcs.DefaultVerifierVersion,
		SourceCommit:    manifest.PFSourceCommit,
		ReleaseMode:     true,
		Handoff:         handoff,
	}
	_, err = pcs.VerifyScienceClaimBundle(path, bundle, opts)
	return err
}

func TestVerifyRejectsChangedCertifiedBundleHash(t *testing.T) {
	h := matchingHandoff(t)
	h.CertifiedBundleHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err := verifyWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected verify to fail on certified bundle hash mismatch")
	}
	if !strings.Contains(err.Error(), "certified_bundle_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestVerifyRejectsChangedCertificateID(t *testing.T) {
	h := matchingHandoff(t)
	h.CertificateID = "cert-trace-00000000-0000-0000-0000-000000000000"
	err := verifyWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected verify to fail on certificate_id mismatch")
	}
	if !strings.Contains(err.Error(), "certificate_id mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestVerifyRejectsChangedTraceHash(t *testing.T) {
	h := matchingHandoff(t)
	h.TraceHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	err := verifyWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected verify to fail on trace_hash mismatch")
	}
	if !strings.Contains(err.Error(), "trace_hash mismatch") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestSignRejectsBundleNotMatchingHandoff(t *testing.T) {
	h := matchingHandoff(t)
	h.CertifiedBundleHash = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
	err := signWithHandoff(t, h)
	if err == nil {
		t.Fatal("expected sign to fail when bundle does not match handoff")
	}
	if !strings.Contains(err.Error(), "handoff") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func TestInspectRejectsTamperedSignedBundle(t *testing.T) {
	signed, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	signed.SignatureOrDigest = "sha256:0000000000000000000000000000000000000000000000000000000000000000"
	integrityErr := pcs.VerifySignedBundleIntegrity(signed, pcs.IntegrityOptions{VerifyPFDigests: true})
	if integrityErr == nil {
		t.Fatal("expected strict inspect integrity to fail on tampered wrapper digest")
	}
	if !strings.Contains(integrityErr.Error(), "digest mismatch") {
		t.Fatalf("unexpected error: %v", integrityErr)
	}

	signed2, err := pcs.LoadSignedScienceClaimBundle(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	if signed2.ScienceClaimBundle != nil && len(signed2.ScienceClaimBundle.Certificates) > 0 {
		signed2.ScienceClaimBundle.Certificates[0].CertificateID = "cert-trace-tampered"
	}
	if err := pcs.VerifySignedBundleIntegrity(signed2, pcs.IntegrityOptions{VerifyPFDigests: false}); err != nil {
		t.Fatal(err)
	}
	if err := pcs.AssertReleaseArtifactChain(
		loadCertifiedBundle(t),
		signed2.VerificationResult,
		signed2,
	); err == nil {
		t.Fatal("expected release chain assert to fail after tampering embedded certificate_id")
	}
}

func inspectFixture(t *testing.T, mutate func(map[string]any)) error {
	t.Helper()
	raw, err := os.ReadFile(labtrustReleaseFixture(t, "signed_science_claim_bundle.json"))
	if err != nil {
		t.Fatal(err)
	}
	var doc map[string]any
	if err := json.Unmarshal(raw, &doc); err != nil {
		t.Fatal(err)
	}
	if mutate != nil {
		mutate(doc)
	}
	path := filepath.Join(t.TempDir(), "signed_mutated.json")
	data, err := json.MarshalIndent(doc, "", "  ")
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, data, 0644); err != nil {
		t.Fatal(err)
	}
	signed, err := pcs.LoadSignedScienceClaimBundle(path)
	if err != nil {
		return err
	}
	return pcs.InspectSignedScienceClaimBundle(repoRoot(t), signed, pcs.IntegrityOptions{VerifyPFDigests: true})
}

func TestInspectRejectsMissingVerificationResult(t *testing.T) {
	err := inspectFixture(t, func(doc map[string]any) {
		delete(doc, "verification_result")
	})
	if err == nil {
		t.Fatal("expected inspect to fail when verification_result is missing")
	}
}

func TestInspectRejectsFailedVerificationResult(t *testing.T) {
	err := inspectFixture(t, func(doc map[string]any) {
		vr, ok := doc["verification_result"].(map[string]any)
		if !ok {
			t.Fatal("verification_result must be an object")
		}
		vr["status"] = "Rejected"
	})
	if err == nil {
		t.Fatal("expected inspect to fail when verification status is Rejected")
	}
	if !strings.Contains(err.Error(), "ProofChecked") {
		t.Fatalf("unexpected error: %v", err)
	}
}

func loadCertifiedBundle(t *testing.T) *pcs.ScienceClaimBundle {
	t.Helper()
	b, err := pcs.LoadScienceClaimBundle(labtrustReleaseFixture(t, "science_claim_bundle.certified.json"))
	if err != nil {
		t.Fatal(err)
	}
	return b
}
